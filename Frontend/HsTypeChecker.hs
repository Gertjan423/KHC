{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} -- George says: God I hate this flag

module Frontend.HsTypeChecker (hsElaborate) where

import Frontend.HsTypes
import Frontend.HsRenamer
import Frontend.Conditions

import Optimizer.FcTypes

import Utils.Substitution
import Utils.FreeVars
import Utils.Var
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Annotated
import Utils.Ctx
import Utils.SnocList
import Utils.PrettyPrint
import Utils.Utils
import Utils.Errors
import Utils.Trace
import Utils.ListT

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Arrow (second)
import Data.List (nub, (\\))

-- * Create the typechecking environment from the renaming one
-- ------------------------------------------------------------------------------

-- | Build the initial typechecker environment from the renaming environment
buildInitTcEnv :: RnProgram -> RnEnv -> TcM ()
buildInitTcEnv pgm (RnEnv _rn_cls_infos dc_infos tc_infos) = do -- GEORGE: Assume that the initial environment is completely empty (mempty mempty mempty)
  -- Prepopulate the environment with the (user-defined) data constructor information
  mapAssocListM_ (uncurry addDataConInfoTcM) $
    mapFstWithDataAssocList (\_ info -> hs_dc_data_con info) dc_infos
  -- Prepopulate the environment with the (user-defined) type constructor information
  mapAssocListM_ (uncurry addTyConInfoTcM)   $
    mapFstWithDataAssocList (\_ info -> hs_tc_ty_con   info) tc_infos
  -- Create and store in the environment all infos for type classes
  -- (and the constructors they give rise to) -- GEORGE: UPDATE THIS WHEN YOU ADD SUPERCLASSES
  buildStoreClsInfos pgm
  where
    buildStoreClsInfos :: RnProgram -> TcM ()
    buildStoreClsInfos (PgmExp {})   = return ()
    buildStoreClsInfos (PgmInst _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmData _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmFunc _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmCls  c p) = case c of
      ClsD rn_cs rn_cls (rn_a :| _kind) rn_method method_ty -> do
        -- Generate And Store The TyCon Info
        rn_tc <- getUniqueM >>= return . HsTC . mkName (mkSym ("T" ++ (show $ symOf rn_cls)))
        let tc_info = HsTCInfo rn_tc [rn_a] (FcTC (nameOf rn_tc))
        addTyConInfoTcM rn_tc tc_info

        -- Generate And Store The DataCon Info
        rn_dc  <- getUniqueM >>= return . HsDC . mkName (mkSym ("K" ++ (show $ symOf rn_cls)))
        let dc_info = HsDCClsInfo rn_dc [rn_a] rn_tc rn_cs [method_ty] (FcDC (nameOf rn_dc))
        addDataConInfoTcM rn_dc dc_info

        -- Generate And Store The Class Info
        let cls_info = ClassInfo rn_cs rn_cls [rn_a] rn_method method_ty rn_tc rn_dc
        addClsInfoTcM rn_cls cls_info

        -- Continue with the rest
        buildStoreClsInfos p

-- | Add a renamed class name to the state
addClsInfoTcM :: RnClass -> ClassInfo -> TcM ()
addClsInfoTcM cls info = modify $ \s ->
  s { tc_env_cls_info = extendAssocList cls info (tc_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoTcM :: RnDataCon -> HsDataConInfo -> TcM ()
addDataConInfoTcM dc info = modify $ \s ->
  s { tc_env_dc_info = extendAssocList dc info (tc_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoTcM :: RnTyCon -> HsTyConInfo -> TcM ()
addTyConInfoTcM tc info = modify $ \s ->
  s { tc_env_tc_info = extendAssocList tc info (tc_env_tc_info s) }

-- * Type Checking Monad
-- ------------------------------------------------------------------------------

type TcM  = UniqueSupplyT 
          ( ReaderT TcCtx 
          ( StateT TcEnv 
          ( ExceptT String 
          ( Writer Trace ) ) ) )

type TcCtx = Ctx RnTmVar RnPolyTy RnTyVar Kind

data TcEnv = TcEnv { tc_env_cls_info :: AssocList RnClass   ClassInfo
                   , tc_env_dc_info  :: AssocList RnDataCon HsDataConInfo
                   , tc_env_tc_info  :: AssocList RnTyCon   HsTyConInfo }

instance PrettyPrint TcEnv where
  ppr (TcEnv cls_infos dc_infos tc_infos)
    = braces $ vcat $ punctuate comma
    [ text "tc_env_cls_info" <+> colon <+> ppr cls_infos
    , text "tc_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "tc_env_tc_info"  <+> colon <+> ppr tc_infos
    ]
  needsParens _ = False

-- | Transform info for a type constructor to the System F variant
elabHsTyConInfo :: HsTyConInfo -> FcTyConInfo
elabHsTyConInfo (HsTCInfo _tc as fc_tc) = FcTCInfo fc_tc (map rnTyVarToFcTyVar as)

elabHsDataConInfo :: HsDataConInfo -> TcM FcDataConInfo
elabHsDataConInfo (HsDCInfo _dc as tc tys fc_dc) = do
  fc_tc  <- lookupTyCon tc
  fc_tys <- map snd <$> extendTcCtxTysM as (mapM wfElabPolyTy tys)
  return $ FcDCInfo fc_dc (map rnTyVarToFcTyVar as) fc_tc fc_tys
elabHsDataConInfo (HsDCClsInfo _dc as tc super tys fc_dc) = do
  fc_tc  <- lookupTyCon tc
  fc_sc  <- extendTcCtxTysM as (mapM elabClsCt super)
  fc_tys <- map snd <$> extendTcCtxTysM as (mapM wfElabPolyTy tys)
  return $ FcDCInfo fc_dc (map rnTyVarToFcTyVar as) fc_tc (fc_sc ++ fc_tys)

buildInitFcAssocs :: TcM (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)
buildInitFcAssocs = do
  -- Convert the tyCon associations
  tc_infos <- gets tc_env_tc_info
  fc_tc_infos <- flip mapAssocListM tc_infos $ \(tc, tc_info) -> do
    fc_tc <- lookupTyCon tc
    return (fc_tc, elabHsTyConInfo tc_info)

  -- Convert the dataCon associations
  dc_infos <- gets tc_env_dc_info
  fc_dc_infos <- flip mapAssocListM dc_infos $ \(dc, dc_info) -> do
    fc_dc      <- lookupDataCon dc
    fc_dc_info <- elabHsDataConInfo dc_info
    return (fc_dc, fc_dc_info)

  return (fc_tc_infos, fc_dc_infos)

-- * Ensure that some things are not bound in the local context
-- ------------------------------------------------------------------------------

-- | Ensure something is not already bound in the local context
notInTcCtxM :: (PrettyPrint a, MonadReader ctx m, MonadError String m) => (ctx -> a -> Maybe t) -> a -> m ()
notInTcCtxM f x = ask >>= \ctx -> case f ctx x of
  Just {} -> throwErrorM (text "notInTcCtxM" <+> colon <+> ppr x <+> text "is already bound")
  Nothing -> return ()

-- | Ensure the type variable is not already bound
tyVarNotInTcCtxM :: RnTyVar -> TcM ()
tyVarNotInTcCtxM = notInTcCtxM lookupTyVarCtx

-- | Ensure the term variable is not already bound
tmVarNotInTcCtxM :: RnTmVar -> TcM ()
tmVarNotInTcCtxM = notInTcCtxM lookupTmVarCtx

-- * Lookup data and type constructors for a class
-- ------------------------------------------------------------------------------

-- GEORGE: 1. Rename TcEnv to TcGblEnv
--         2. It's exactly the same as lookupFcGblEnv. Abstract over both.

-- | Lookup something in the global environment
lookupTcEnvM ::  (Eq a, PrettyPrint a, MonadError String m, MonadState s m) => (s -> AssocList a b) -> a -> m b
lookupTcEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> throwErrorM (text "lookupTcEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup a type constructor
lookupTyCon :: RnTyCon -> TcM FcTyCon
lookupTyCon tc = hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc

-- | Lookup the kind of a type constructor
tyConKind :: RnTyCon -> TcM Kind
tyConKind tc = do
  info <- lookupTcEnvM tc_env_tc_info tc
  return (mkArrowKind (map kindOf (hs_tc_type_args info)) KStar)

-- | Lookup a data constructor
lookupDataCon :: RnDataCon -> TcM FcDataCon
lookupDataCon dc = hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc

-- | Lookup the kinds of the arguments
clsArgKinds :: RnClass -> TcM [Kind]
clsArgKinds cls = lookupTcEnvM tc_env_cls_info cls >>= return . map kindOf . cls_type_args

-- | Lookup the System Fc type constructor for a class
lookupClsTyCon :: RnClass -> TcM FcTyCon
lookupClsTyCon cls = do
  hs_tycon <- cls_tycon <$> lookupTcEnvM tc_env_cls_info cls
  hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info hs_tycon

-- | Lookup the System Fc data constructor for a class
lookupClsDataCon :: RnClass -> TcM FcDataCon
lookupClsDataCon cls = do
  hs_datacon <- cls_datacon <$> lookupTcEnvM tc_env_cls_info cls
  hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info hs_datacon

-- | Get the signature of a data constructor in pieces
dataConSig :: RnDataCon -> TcM ([RnTyVar], [RnPolyTy], RnTyCon) -- GEORGE: Needs to take into account the class case too
dataConSig dc = lookupTcEnvM tc_env_dc_info dc >>= \info ->
  return ( hs_dc_univ    info
         , hs_dc_arg_tys info
         , hs_dc_parent  info )

-- | Get the superclasses of a class
lookupClsSuper :: RnClass -> TcM RnClsCs
lookupClsSuper cls = cls_super <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the parameter of the class
lookupClsParam :: RnClass -> TcM RnTyVar
lookupClsParam cls = do
  info <- lookupTcEnvM tc_env_cls_info cls
  case cls_type_args info of
    [a] -> return a
    _   -> throwErrorM (text "lookupClsParam")

-- * Type and Constraint Elaboration (With Well-formedness (well-scopedness) Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
wfElabMonoTy :: RnMonoTy -> TcM (Kind, FcType)
wfElabMonoTy (TyCon tc) = do
  kind  <- tyConKind tc
  fc_tc <- lookupTyCon tc
  return (kind, FcTyCon fc_tc)
wfElabMonoTy (TyApp ty1 ty2) = do
  (k1, fc_ty1) <- wfElabMonoTy ty1
  (k2, fc_ty2) <- wfElabMonoTy ty2
  case k1 of
    KArr k1a k1b
      | k1a == k2 -> return (k1b, FcTyApp fc_ty1 fc_ty2)
    _other_kind   -> throwErrorM (text "wfElabMonoTy" <+> colon <+> text "TyApp")
wfElabMonoTy (TyVar v) = do
  kind <- lookupTyVarM v
  return (kind, rnTyVarToFcType v)

-- | Elaborate a qualified type
wfElabQualTy :: RnQualTy -> TcM (Kind, FcType)
wfElabQualTy (QMono ty)    = wfElabMonoTy ty
wfElabQualTy (QQual ct ty) = do
  fc_ty1         <- wfElabClsCt ct
  (kind, fc_ty2) <- wfElabQualTy ty
  unless (kind == KStar) $
    throwErrorM (text "wfElabQualTy" <+> colon <+> text "QQual")
  return (KStar, mkFcArrowTy fc_ty1 fc_ty2)

-- | Elaborate a class constraint
wfElabClsCt :: RnClsCt -> TcM FcType
wfElabClsCt (ClsCt cls ty) = do
  (ty_kind, fc_ty) <- wfElabMonoTy ty
  clsArgKinds cls >>= \case
    [k] | k == ty_kind -> do
      fc_tc <- lookupClsTyCon cls
      return (FcTyApp (FcTyCon fc_tc) fc_ty)
    _other_kind -> throwErrorM (text "wfElabCtr" <+> colon <+> text "CtrClsCt")

-- | Elaborate a constraint
wfElabCtr :: RnCtr -> TcM FcType
wfElabCtr (Ctr []  []     ct) = wfElabClsCt ct
wfElabCtr (Ctr []  (c:cs) ct) = mkFcArrowTy <$> wfElabClsCt c <*> wfElabCtr (Ctr [] cs ct)
wfElabCtr (Ctr ((a :| k):as) cs  ct) = do
  tyVarNotInTcCtxM a
  FcTyAbs (rnTyVarToFcTyVar a) <$> (extendCtxTyM a k (wfElabCtr (Ctr as cs ct)))

-- | Elaborate a list of class constraints
wfElabClsCs :: RnClsCs -> TcM [FcType]
wfElabClsCs = mapM wfElabClsCt

-- | Elaborate a polytype
wfElabPolyTy :: RnPolyTy -> TcM (Kind, FcType)
wfElabPolyTy (PQual ty) = wfElabQualTy ty
wfElabPolyTy (PPoly (a :| _) ty) = do
  tyVarNotInTcCtxM a {- GEORGE: ensure is unbound -}
  (kind, fc_ty) <- extendCtxTyM a (kindOf a) (wfElabPolyTy ty)
  unless (kind == KStar) $
    throwErrorM (text "wfElabPolyTy" <+> colon <+> text "PPoly")
  return (KStar, FcTyAbs (rnTyVarToFcTyVar a) fc_ty)

-- * Type and Constraint Elaboration (Without Well-scopedness Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
elabMonoTy :: RnMonoTy -> TcM FcType
elabMonoTy (TyCon tc)      = FcTyCon <$> lookupTyCon tc
elabMonoTy (TyApp ty1 ty2) = FcTyApp <$> elabMonoTy ty1 <*> elabMonoTy ty2
elabMonoTy (TyVar v)       = return (rnTyVarToFcType v)

-- | Elaborate a class constraint (DO NOT CHECK WELL-SCOPEDNESS)
elabClsCt :: RnClsCt -> TcM FcType
elabClsCt (ClsCt cls ty)
  = FcTyApp <$> (FcTyCon <$> lookupClsTyCon cls) <*> elabMonoTy ty

-- | Elaborate a constraint (DO NOT CHECK WELL-SCOPEDNESS)
-- GEORGE: Check kinds though!!
elabCtr :: RnCtr -> TcM FcType
elabCtr (Ctr []  []     ct) = elabClsCt ct
elabCtr (Ctr []  (c:cs) ct) = mkFcArrowTy <$> (elabClsCt c) <*> elabCtr (Ctr [] cs ct)
elabCtr (Ctr (a:as) cs  ct) = FcTyAbs (rnTyVarToFcTyVar (labelOf a)) <$> elabCtr (Ctr as cs ct)

-- * Constraint Solving Monad
-- ------------------------------------------------------------------------------

newtype SolveM a = SolveM (ListT TcM a)
  deriving ( Functor, Applicative, Monad
           , MonadState TcEnv, MonadReader TcCtx, MonadError String )

instance MonadUnique SolveM where
  getUniqueSupplyM = liftSolveM getUniqueSupplyM

-- | Lift TcM into SolveM
liftSolveM :: TcM a -> SolveM a
liftSolveM m = SolveM (lift m)

-- | Get the first solution
runSolverFirstM :: SolveM a -> TcM a
runSolverFirstM (SolveM m) = firstListT m

-- * Constraint store
-- ------------------------------------------------------------------------------

-- | ConstraintStore containing both the equality constraints and named class constraints
data ConstraintStore = CS EqCs AnnClsCs

instance Semigroup ConstraintStore where
  (<>) (CS eqs1 ccs1) (CS eqs2 ccs2)
    = CS (eqs1 <> eqs2) (ccs1 <> ccs2)

instance Monoid ConstraintStore where
  mempty = CS mempty mempty

-- | Type inference generation monad
newtype GenM a = GenM (StateT ConstraintStore TcM a)
  deriving ( Functor, Applicative, Monad
           , MonadState ConstraintStore, MonadReader TcCtx, MonadError String )

-- GEORGE: All this is bad. We should not store the unique supply within the
-- global environment, rather wrap our monads with the UniqueSupplyT transformer
instance MonadUnique GenM where
  getUniqueSupplyM = liftGenM getUniqueSupplyM

-- | Get out of the constraint generation monad
runGenM :: GenM a -> TcM (a, EqCs, AnnClsCs)
runGenM (GenM m) = do
    (v , (CS eqs ccs)) <- runStateT m mempty
    return (v, eqs, ccs)

-- | Lift TcM into GenM
liftGenM :: TcM a -> GenM a
liftGenM m = GenM (StateT (\cs -> m >>= \x -> return (x, cs)))

-- | Add some equality constraints in the constraint store
storeEqCs :: EqCs -> GenM ()
storeEqCs cs = modify (\(CS eqs ccs) -> CS (cs ++ eqs) ccs)

-- | Add some (variable-annotated) class constraints in the constraint store
storeAnnCts :: AnnClsCs -> GenM ()
storeAnnCts cs = modify (\(CS eqs ccs) -> CS eqs (mappend ccs cs))

-- | Add many type variables to the typing context
extendTcCtxTysM :: MonadReader TcCtx m => [RnTyVar] -> m a -> m a
extendTcCtxTysM []     m = m
extendTcCtxTysM (a:as) m = extendCtxTyM a (kindOf a) (extendTcCtxTysM as m) -- just a left fold..

-- | Set the typing environment
setTcCtxTmM :: MonadReader TcCtx m => TcCtx -> m a -> m a
setTcCtxTmM ctx = local (\_ -> ctx)

-- * Term Elaboration
-- ------------------------------------------------------------------------------

-- | Freshen up a list of type variables. Return
--   a) the list of fresh variables (NB: same length as input)
--   b) the substitution from the old to the fresh ones
freshenRnTyVars :: [RnTyVar] -> TcM ([RnTyVar], HsTySubst)
freshenRnTyVars tvs = do
  new_tvs <- mapM freshRnTyVar (map kindOf tvs)
  let subst = buildRnSubst (zipExact tvs new_tvs)
  return (new_tvs, subst)

-- | Instantiate a polytype with fresh unification variables
instPolyTy :: RnPolyTy -> TcM ([RnTyVar], RnClsCs, RnMonoTy)
instPolyTy poly_ty = do
  (bs, subst) <- freshenRnTyVars (map labelOf as)
  let new_cs = substInClsCs subst cs
  let new_ty = substInMonoTy subst ty
  return (bs, new_cs, new_ty)
  where
    (as, cs, ty) = destructPolyTy poly_ty

-- | Generate a number of fresh dictionary variables
genFreshDictVars :: MonadUnique m => Int -> m [DictVar]
genFreshDictVars n = replicateM n freshDictVar

-- | Annotate a list of constraints with a fresh dictionary variables
-- annotateCts :: RnCts -> TcM ([DictVar], AnnCts)
-- annotateCts cs = do
--   ds <- genFreshDictVars (length cs)
--   return (ds, (listToSnocList ds) |: (listToSnocList cs))

-- | Annotate a list of class constraints with a fresh dictionary variables
annotateClsCs :: RnClsCs -> TcM ([DictVar], SimpleProgramTheory)
annotateClsCs cs = do
  ds <- genFreshDictVars (length cs)
  return (ds, (listToSnocList ds) |: (listToSnocList cs))

-- | Elaborate a term
elabTerm :: RnTerm -> GenM (RnMonoTy, FcTerm)
elabTerm (TmApp tm1 tm2)   = elabTmApp tm1 tm2
elabTerm (TmAbs x tm)      = elabTmAbs x tm
elabTerm (TmVar x)         = elabTmVar x
elabTerm (TmCon dc)        = liftGenM (elabTmCon dc)
elabTerm (TmLet x tm1 tm2) = elabTmLet x tm1 tm2
elabTerm (TmCase scr alts) = elabTmCase scr alts

-- | Elaborate a term application
elabTmApp :: RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmApp tm1 tm2 = do
  (ty1, fc_tm1) <- elabTerm tm1
  (ty2, fc_tm2) <- elabTerm tm2
  a <- TyVar <$> freshRnTyVar KStar
  storeEqCs [mkRnArrowTy [ty2] a :~: ty1]
  return (a, FcTmApp fc_tm1 fc_tm2)

-- | Elaborate a lambda abstraction
elabTmAbs :: RnTmVar -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmAbs x tm = do
  liftGenM (tmVarNotInTcCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty, fc_tm) <- extendCtxTmM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm
  let result = FcTmAbs (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm
  return (mkRnArrowTy [TyVar tv] ty, result)

-- | Elaborate a term variable
elabTmVar :: RnTmVar -> GenM (RnMonoTy, FcTerm)
elabTmVar x = do
  poly_ty     <- liftGenM (lookupTmVarM x)
  (bs,cs,ty)  <- liftGenM (instPolyTy poly_ty)
  _           <- extendTcCtxTysM bs $ liftGenM (wfElabClsCs cs) -- Check well formedness of the constraints
  (ds,ann_cs) <- liftGenM (annotateClsCs cs)
  storeAnnCts $ ann_cs -- store the constraints
  let fc_ds = map FcTmVar ds         -- System F representation
  let fc_bs = map rnTyVarToFcType bs -- System F representation
  let fc_tm = fcTmApp (fcTmTyApp (rnTmVarToFcTerm x) fc_bs) fc_ds
  return (ty, fc_tm)

-- | Elaborate a let binding (monomorphic, recursive)
elabTmLet :: RnTmVar -> RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmLet x tm1 tm2 = do
  liftGenM (tmVarNotInTcCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty1, fc_tm1) <- extendCtxTmM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm1
  (ty2, fc_tm2) <- extendCtxTmM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm2 -- could have also passed ty1 but it is the same
  storeEqCs [TyVar tv :~: ty1]
  let fc_tm = FcTmLet (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm1 fc_tm2
  return (ty2, fc_tm)

-- | Elaborate a data constructor
elabTmCon :: RnDataCon -> TcM (RnMonoTy, FcTerm)
elabTmCon dc = do
  (bs, arg_tys, tc) <- freshenDataConSig dc
  fc_dc <- lookupDataCon dc

  let mono_ty = mkRnArrowTy arg_tys (mkTyConApp tc (map TyVar bs))                 -- Haskell monotype
  let fc_tm = fcTmTyApp (FcTmDataCon fc_dc) (rnTyVarsToFcTypes bs) -- System F term

  return (mono_ty, fc_tm)

freshenDataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
freshenDataConSig dc = do
  (as, poly_arg_tys, tc) <- dataConSig dc
  (bs, subst) <- freshenRnTyVars as                              -- Freshen up the universal type variables
  arg_tys     <- polyTysToMonoTysM $ map (substInPolyTy subst) poly_arg_tys -- Substitute in the argument types
  return (bs, arg_tys, tc)

-- | Cast a list of polytypes to monotypes. Fail if not possible
polyTysToMonoTysM :: MonadError String m => [PolyTy a] -> m [MonoTy a]
polyTysToMonoTysM []       = return []
polyTysToMonoTysM (ty:tys) = case polyTyToMonoTy ty of
  Just mono_ty -> fmap (mono_ty:) (polyTysToMonoTysM tys)
  Nothing      -> throwErrorM (text "polyTysToMonoTysM" <+> colon <+> text "non-monotype")

-- | Elaborate a case expression
elabTmCase :: RnTerm -> [RnAlt] -> GenM (RnMonoTy, FcTerm)
elabTmCase scr alts = do
  (scr_ty, fc_scr) <- elabTerm scr               -- Elaborate the scrutinee
  rhs_ty  <- TyVar <$> freshRnTyVar KStar        -- Generate a fresh type variable for the result
  fc_alts <- mapM (elabHsAlt scr_ty rhs_ty) alts -- Check the alternatives
  return (rhs_ty, FcTmCase fc_scr fc_alts)

-- | Elaborate a case alternative
elabHsAlt :: RnMonoTy {- Type of the scrutinee -}
          -> RnMonoTy {- Result type           -}
          -> RnAlt    {- Case alternative      -}
          -> GenM FcAlt
elabHsAlt scr_ty res_ty (HsAlt (HsPat dc xs) rhs) = do
  (as, orig_arg_tys, tc) <- liftGenM (dataConSig dc) -- Get the constructor's signature
  fc_dc <- liftGenM (lookupDataCon dc)               -- Get the constructor's System F representation

  (bs, ty_subst) <- liftGenM (freshenRnTyVars as)               -- Generate fresh universal type variables for the universal tvs
  let arg_tys = map (substInPolyTy ty_subst) orig_arg_tys       -- Apply the renaming substitution to the argument types
  (rhs_ty, fc_rhs) <- extendCtxTmsM xs arg_tys (elabTerm rhs)   -- Type check the right hand side
  storeEqCs [ scr_ty :~: foldl TyApp (TyCon tc) (map TyVar bs)  -- The scrutinee type must match the pattern type
            , res_ty :~: rhs_ty ]                               -- All right hand sides should be the same

  return (FcAlt (FcConPat fc_dc (map rnTmVarToFcTmVar xs)) fc_rhs)

-- | Covert a renamed type variable to a System F type
rnTyVarToFcType :: RnTyVar -> FcType
rnTyVarToFcType = FcTyVar . rnTyVarToFcTyVar

-- | Covert a list of renamed type variables to a list of System F types
rnTyVarsToFcTypes :: [RnTyVar] -> [FcType]
rnTyVarsToFcTypes = map rnTyVarToFcType

-- | Covert a renamed term variable to a System F term
rnTmVarToFcTerm :: RnTmVar -> FcTerm
rnTmVarToFcTerm = FcTmVar . rnTmVarToFcTmVar

-- * Type Unification
-- ------------------------------------------------------------------------------

-- | Type Unification. The first argument are the untouchables (rigid) variables.
unify :: MonadError String m => [RnTyVar] -> EqCs -> m HsTySubst
unify _untchs [] = return mempty
unify  untchs eqs
  | Just ((subst1, eqs'), eqs'') <- go (one_step untchs) eqs
  = do subst2 <- unify untchs (substInEqCs subst1 (eqs' ++ eqs''))
       return (subst2 <> subst1)
  | otherwise = throwErrorM $ vcat [ text "Unification failed."
                                   , text "Residual constraints" <+> colon <+> ppr eqs
                                   , text "Untouchables"         <+> colon <+> ppr untchs ]
  where
    one_step :: [RnTyVar] -> EqCt -> Maybe (HsTySubst, EqCs)
    one_step _us (TyVar v1 :~: TyVar v2)
      | v1 == v2 = Just (mempty, [])
    one_step us (TyVar v :~: ty)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
      | otherwise                        = Nothing
    one_step us (ty :~: TyVar v)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
      | otherwise                        = Nothing
    one_step _us (TyCon tc1 :~: TyCon tc2)
      | tc1 == tc2 = Just (mempty, [])
      | otherwise  = Nothing
    one_step _us (TyApp ty1 ty2 :~: TyApp ty3 ty4)
      = Just (mempty, [ty1 :~: ty3, ty2 :~: ty4])
    one_step _us (TyCon {} :~: TyApp {}) = Nothing
    one_step _us (TyApp {} :~: TyCon {}) = Nothing

    go :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
    go _p []     = Nothing
    go  p (x:xs) | Just y <- p x = Just (y, xs)
                 | otherwise     = second (x:) <$> go p xs

-- | Occurs Check
occursCheck :: RnTyVar -> RnMonoTy -> Bool
occursCheck _ (TyCon {})      = True
occursCheck a (TyApp ty1 ty2) = occursCheck a ty1 && occursCheck a ty2
occursCheck a (TyVar b)       = a /= b

-- * Overlap Checking
-- ------------------------------------------------------------------------------

overlapCheck :: MonadError String m => FullTheory -> RnClsCt -> m ()
overlapCheck theory cls_ct@(ClsCt cls1 ty1) = case lookupSLMaybe overlaps (theory_inst theory) of -- We only care about the instance theory
  Just msg -> throwErrorM msg
  Nothing  -> return ()
  where
    overlaps (_ :| ctr)
      | ClsCt cls2 ty2 <- ctrHead ctr
      , cls1 == cls2
      , Right {} <- unify [] [ty1 :~: ty2]
      = Just (text "overlapCheck:" $$ ppr cls_ct $$ ppr ctr)
      | otherwise = Nothing

-- * Constraint Entailment
-- ------------------------------------------------------------------------------

-- | Completely entail a set of constraints. Fail if not possible
entailTcM :: [RnTyVar] -> ProgramTheory -> SimpleProgramTheory -> TcM FcTmSubst
entailTcM untch theory ctrs = runSolverFirstM (go ctrs)
  where
    go SN        = return mempty
    go (cs :> c) = do
      (ccs, subst1) <- rightEntailsBacktrack untch theory c
      subst2 <- go (cs <> ccs)
      return (subst2 <> subst1)

-- | Exhaustively simplify a set of constraints (this version does not backtrack)
entailDetTcM :: [RnTyVar] -> ProgramTheory -> SimpleProgramTheory -> TcM (SimpleProgramTheory, FcTmSubst)
entailDetTcM untch theory ctrs = go ctrs
  where
    entail_one :: AnnClsCt -> TcM (Maybe (SimpleProgramTheory, FcTmSubst))
    entail_one = rightEntailsDet untch theory

    go :: SimpleProgramTheory -> TcM (SimpleProgramTheory, FcTmSubst)
    go cs = findSLMaybeM entail_one cs >>= \case
      Just (rest, (simp_cs, subst1)) -> do
        (final_cs, subst2) <- go (rest <> simp_cs)
        return (final_cs, subst2 <> subst1)
      Nothing -> return (cs, mempty)

-- | Performs a single right entailment step.
--   a) fail if the constraint is not entailed by the given program theory
--   b) return the new wanted (class) constraints, as well as the System F term subsitution
rightEntailsDet :: [RnTyVar] -> ProgramTheory -> AnnClsCt
                -> TcM (Maybe (SimpleProgramTheory, FcTmSubst))
rightEntailsDet untch theory ann_cls_ct = lookupSLMaybeM left_entails theory
  where
    left_entails ct = leftEntails untch ct ann_cls_ct

-- | Performs a single right entailment step.
--   a) fail if the constraint is not entailed by the given program theory
--   b) return the new wanted (class) constraints, as well as the System F term subsitution
rightEntailsBacktrack :: [RnTyVar] -> ProgramTheory -> AnnClsCt
                      -> SolveM (SimpleProgramTheory, FcTmSubst)
rightEntailsBacktrack untch theory ann_cls_ct = liftSolveM (snocListChooseM theory left_entail) >>= SolveM . selectListT
  where
    left_entail ann_ctr = leftEntails untch ann_ctr ann_cls_ct

-- | Checks whether the class constraint is entailed by the given constraint
--   a) fails if the class constraint is not entailed
--   b) return the new wanted constraints, as well as the System F term substitution
leftEntails :: [RnTyVar] -> AnnCtr -> AnnClsCt
            -> TcM (Maybe (SimpleProgramTheory, FcTmSubst))
leftEntails untch (d_g :| ctr_g) (d_w :| cls_ct_w) = do
  (Ctr as cls_cs cls_ct_g) <- freshenLclBndrs ctr_g
  matchClsCs untch (d_g :| cls_ct_g) (d_w :| cls_ct_w) >>= \case
    Nothing            -> return Nothing
    Just (ty_subst, _) -> do
      (residual_ccs , d_res)   <- constructResidualCcs ty_subst cls_cs
      ev_subst_tm              <- constructEvFcTerm ty_subst (FcTmVar d_g) as d_res
      let ev_subst             = d_w |-> ev_subst_tm
      return $ Just (residual_ccs , ev_subst)
  where
    constructResidualCcs :: HsTySubst -> [RnClsCt] -> TcM (SimpleProgramTheory, [DictVar])
    constructResidualCcs _ty_subst []     = return (mempty , [])
    constructResidualCcs  ty_subst (c:cs) = do
      d             <- freshDictVar
      let subst_c   = substInClsCt ty_subst c
      (ann_cs , ds) <- constructResidualCcs ty_subst cs
      return (ann_cs :> (d :| subst_c) , d : ds)

    constructEvFcTerm :: HsTySubst -> FcTerm -> [RnTyVarWithKind] -> [DictVar] -> TcM FcTerm
    constructEvFcTerm _ty_subst fc_tm []     []     = return fc_tm
    constructEvFcTerm  ty_subst fc_tm []     (d:ds) =
      constructEvFcTerm ty_subst (FcTmApp fc_tm (FcTmVar d)) [] ds
    constructEvFcTerm  ty_subst fc_tm (a:as) ds     =
      elabMonoTy (substInMonoTy ty_subst (TyVar (labelOf a))) >>= \subst_fc_ty ->
      constructEvFcTerm ty_subst (FcTmTyApp fc_tm subst_fc_ty) as ds

-- | Unify two annotated class constraints (check that they have the same class
-- name and that the arguments can be unified). Return the resulting type and
-- term substitution.
matchClsCs :: Monad m => [RnTyVar] -> AnnClsCt {- Given -} -> AnnClsCt {- Wanted -}
           -> m (Maybe (HsTySubst, FcTmSubst))
matchClsCs untch (d1 :| ClsCt cls1 ty1) (d2 :| ClsCt cls2 ty2)
  | cls1 == cls2
  , Right ty_subst <- unify untch [ty1 :~: ty2]
  = return $ Just (ty_subst, d2 |-> FcTmVar d1)
  | otherwise = return Nothing

-- | Elaborate a class declaration. Return
--   a) The data declaration for the class
--   b) The method implementation
--   c) The extended typing environment
elabClsDecl :: RnClsDecl -> TcM (FcDataDecl, FcValBind, [FcValBind], ProgramTheory, TcCtx)
elabClsDecl (ClsD rn_cs cls (a :| _) method method_ty) = do
  -- Generate a fresh type and data constructor for the class
  -- GEORGE: They should already be generated during renaming.
  tc <- lookupClsTyCon   cls
  dc <- lookupClsDataCon cls

  -- Elaborate the superclass constraints (with full well-formedness checking also)
  fc_sc_tys <- extendCtxTyM a (kindOf a) (mapM wfElabClsCt rn_cs)

  -- Elaborate the method type (with full well-formedness checking also)
  (_kind, fc_method_ty) <- extendCtxTyM a (kindOf a) (wfElabPolyTy method_ty)

  -- Generate the datatype declaration
  let fc_data_decl = FcDataDecl tc [rnTyVarToFcTyVar a] [(dc, fc_sc_tys ++ [fc_method_ty])]

  -- Generate the method implementation
  (fc_val_bind, hs_method_ty) <- elabMethodSig method a cls method_ty

  -- Construct the extended typing environment
  ty_ctx <- extendCtxTmM method hs_method_ty ask

  (sc_schemes, sc_decls) <- fmap unzip $ forM (zip [0..] rn_cs) $ \(i,sc_ct) -> do
    d  <- freshDictVar -- For the declaration
    da <- freshDictVar -- For the input dictionary

    let cls_head  = ClsCt cls (TyVar a) -- TC a
    fc_cls_head <- elabClsCt cls_head   -- T_TC a

    let scheme = constructCtr ([a :| kindOf a], [cls_head], sc_ct) -- forall a. TC a => SC
    fc_scheme <- elabCtr scheme                                    -- forall a. T_TC a -> upsilon_SC

    xs <- replicateM (length rn_cs + 1) freshFcTmVar               -- n+1 fresh variables

    let fc_tm = FcTmTyAbs (rnTyVarToFcTyVar a) $
                  FcTmAbs da fc_cls_head $
                    FcTmCase (FcTmVar da)
                             [FcAlt (FcConPat dc xs) (FcTmVar (xs !! i))]
    let proj = FcValBind d fc_scheme fc_tm

    return (d :| scheme, proj) -- error "NOT IMPLEMENTED YET"

  return (fc_data_decl, fc_val_bind, sc_decls, listToSnocList sc_schemes, ty_ctx)

-- | Elaborate a method signature to
--   a) a top-level binding
--   b) the actual source type (with the proper class qualification)
elabMethodSig :: RnTmVar -> RnTyVar -> RnClass-> RnPolyTy -> TcM (FcValBind, RnPolyTy)
elabMethodSig method a cls sigma = do
  -- Create the actual type, freshen it up and take it apart
  (bs, cs, ty) <- instPolyTy (mkRealMethodTy a cls sigma)

  -- Source and target method types
  let method_ty = constructPolyTy (zipWithExact (:|) bs (map kindOf bs), cs, ty)
  (_kind, fc_method_ty) <- wfElabPolyTy method_ty

  -- Annotate the constraints with fresh dictionary variables
  (ds, ann_cs) <- annotateClsCs cs

  dc <- lookupClsDataCon cls  -- pattern constructor
  n  <- length <$> lookupClsSuper cls
  xs <- replicateM (n+1) freshFcTmVar -- n superclass variables + 1 for the method

  -- elaborate the annotated dictionary variables to System F term binders
  dbinds <- annClsCsToTmBinds $ ann_cs

  let rn_bs = map rnTyVarToFcType bs

  let fc_method_rhs = fcTmTyAbs (map rnTyVarToFcTyVar bs) $
                        fcTmAbs dbinds $
                          FcTmCase (FcTmVar (head ds))
                                   [FcAlt (FcConPat dc xs)
                                          (fcDictApp (fcTmTyApp (FcTmVar (last xs)) (tail rn_bs)) (tail ds))]

  let fc_val_bind = FcValBind (rnTmVarToFcTmVar method) fc_method_ty fc_method_rhs

  return (fc_val_bind, method_ty)

-- | Construct the real method type out of the class specification
-- (a, TC, forall bs. C => ty) ~~~~~> forall a bs. (TC a, C) => ty
mkRealMethodTy :: RnTyVar -> RnClass -> RnPolyTy -> RnPolyTy
mkRealMethodTy a cls polyty = case destructPolyTy polyty of
  (bs, cs, ty) -> constructPolyTy ((a :| kindOf a) : bs, (ClsCt cls (TyVar a)) : cs, ty)

-- | Elaborate a list of annotated dictionary variables to a list of System F term binders.
annClsCsToTmBinds :: SimpleProgramTheory -> TcM [(FcTmVar, FcType)]
annClsCsToTmBinds annClsCs = mapM (\(d :| ct) -> elabCtr (constructCtr ([],[],ct)) >>= \ty -> return (d, ty)) $ snocListToList annClsCs

-- * Data Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a datatype declaration
elabDataDecl :: RnDataDecl -> TcM FcDataDecl
elabDataDecl (DataD tc as dcs) = do
  fc_tc <- hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc  -- Elaborate the type constructor
  let fc_as = map (rnTyVarToFcTyVar . labelOf) as              -- Elaborate the universal type variables

  fc_dcs <- forM dcs $ \(dc, tys) -> do
    fc_dc <- hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc         -- Elaborate the data constructor
    (kinds, fc_tys) <- unzip <$> extendCtxKindAnnotatedTysM as (mapM wfElabMonoTy tys) -- Elaborate the argument types
    unless (all (==KStar) kinds) $
      throwErrorM (text "elabDataDecl" <+> colon <+> text "not all datacon args have kind star")
    return (fc_dc, fc_tys)
  return (FcDataDecl fc_tc fc_as fc_dcs)

-- | Extend the typing environment with some kind annotated type variables
extendCtxKindAnnotatedTysM :: (MonadReader (Ctx x x' a Kind) m, Kinded a, MonadError String m) => [Ann a t] -> m b -> m b
extendCtxKindAnnotatedTysM ann_as = extendCtxTysM as (map kindOf as)
  where
    as = map labelOf ann_as

-- * Function Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a function declaration
elabFuncDecl :: FullTheory -> RnFuncDecl
             -> TcM (FcValBind, TcCtx)
elabFuncDecl theory (FuncD func func_ty func_tm) = do
  -- Construct the extended typing environment
  ty_ctx <- extendCtxTmM func func_ty ask

  -- Elaborate function type
  (_kind, fc_func_ty) <- wfElabPolyTy func_ty

  -- Elaborate function term
  (fc_tm) <- setTcCtxTmM ty_ctx (elabTermWithSig [] theory func_tm func_ty)

  -- Resulting binding
  let fc_val_bind = FcValBind (rnTmVarToFcTmVar func) fc_func_ty fc_tm

  return (fc_val_bind, ty_ctx)

-- * Class Instance Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a class instance. Take the program theory also as input and return
--   a) The dictionary transformer implementation
--   b) The extended program theory
elabInsDecl :: FullTheory -> RnInsDecl -> TcM (FcValBind, FullTheory)
elabInsDecl theory (InsD ins_ctx cls typat method method_tm) = do
  -- Ensure the instance does not overlap
  overlapCheck theory head_ct

  -- Create the instance constraint scheme
  ins_d <- freshDictVar
  let ins_scheme = ins_d |: constructCtr (bs, ins_ctx, head_ct)

  --  Generate fresh dictionary variables for the instance context
  ann_ins_ctx <- snd <$> annotateClsCs ins_ctx

  --  The local program theory
  let local_theory = theory `ftExtendLocal` progTheoryFromSimple ann_ins_ctx

  -- The extended program theory
  let ext_theory = theory `ftExtendInst` singletonSnocList ins_scheme

  -- Create the dictionary transformer type
  dtrans_ty <- do
    fc_head_ty <- extendTcCtxTysM (map labelOf bs) (wfElabCtr (constructCtr ([],[],head_ct)))
    fc_ins_ctx <- extendTcCtxTysM (map labelOf bs) (wfElabClsCs ins_ctx)
    return $ fcTyAbs fc_bs $ fcTyArr fc_ins_ctx fc_head_ty

  -- Elaborate the method implementation
  let local_method_theory = local_theory `ftExtendLocal` singletonSnocList ins_scheme
  fc_method_tm <- do
    expected_method_ty <- instMethodTy (hsTyPatToMonoTy typat) <$> lookupTmVarM method
    elabTermWithSig (map labelOf bs) local_method_theory method_tm expected_method_ty

  -- Entail the superclass constraints
  fc_super_tms <- do
    a <- lookupClsParam cls
    (ds, super_cs) <- lookupClsSuper cls                          >>=
                      return . substVar a (hsTyPatToMonoTy typat) >>=
                      annotateClsCs

    ev_subst <- entailTcM (map labelOf bs) (ftToProgramTheory local_theory) super_cs
    --(residual_cs, ev_subst) <- rightEntailsRec (map labelOf bs) (ftToProgramTheory local_theory) super_cs
    --unless (nullSnocList residual_cs) $
    --  throwErrorM (text "Failed to resolve superclass constraints" <+> colon <+> ppr residual_cs
    --               $$ text "From" <+> colon <+> ppr local_theory)

    return (map (substFcTmInTm ev_subst . FcTmVar) ds)

  -- The full implementation of the dictionary transformer
  fc_dict_transformer <- do
    binds <- annClsCsToTmBinds ann_ins_ctx
    dc    <- lookupClsDataCon cls
    pat_ty <- elabMonoTy (hsTyPatToMonoTy typat)
    return $ fcTmTyAbs fc_bs $
               fcTmAbs binds $
                 fcDataConApp dc pat_ty (fc_super_tms ++ [fc_method_tm])

  -- Resulting dictionary transformer
  let fc_val_bind = FcValBind ins_d dtrans_ty fc_dict_transformer

  return (fc_val_bind, ext_theory)
  where
    bs      = ftyvsOf typat
    fc_bs   = map (rnTyVarToFcTyVar . labelOf) bs
    head_ct = ClsCt cls (hsTyPatToMonoTy typat)

-- | Instantiate a method type for a particular instance
instMethodTy :: RnMonoTy -> RnPolyTy -> RnPolyTy
instMethodTy typat poly_ty = constructPolyTy (new_as, new_cs, new_ty)
  where
    ((a :| _kind):as,_c:cs,ty) = destructPolyTy poly_ty
    subst      = (a |-> typat)
    new_as     = as
    new_cs     = substInClsCs subst cs
    new_ty     = substInMonoTy subst ty

-- | Elaborate a term with an explicit type signature (method implementation).
-- This involves both inference and type subsumption.
elabTermWithSig :: [RnTyVar] -> FullTheory -> RnTerm -> RnPolyTy -> TcM FcTerm
elabTermWithSig untch theory tm poly_ty = do

  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  -- Generate fresh dictionary variables for the given constraints
  given_ccs <- snd <$> annotateClsCs cs
  dbinds    <- annClsCsToTmBinds given_ccs

  -- Resolve all the wanted constraints
  let untouchables = nub (untch ++ map labelOf as)

  ty_subst  <- unify untouchables $ wanted_eqs ++ [mono_ty :~: ty]

  ev_subst <- do
    let local_theory = ftToProgramTheory theory <> progTheoryFromSimple given_ccs
    let wanted       = substInSimpleProgramTheory ty_subst wanted_ccs
    -- rightEntailsRec untouchables local_theory wanted
    entailTcM untouchables local_theory wanted

  -- -- Ensure that the constraints are completely resolved
  -- unless (nullSnocList residual_cs) $
  --   throwErrorM (text "Failed to resolve constraints" <+> colon <+> ppr residual_cs
  --                $$ text "From" <+> colon <+> ppr theory)

  fc_subst <- elabHsTySubst ty_subst

  -- The resulting System F term where:
  --   for every type variable that did not get a unique solution during unification,
  --   the variable occurs freely in the term (we refer to them as unresolved vars)
  let refined_fc_tm = fcTmTyAbs fc_as $
                        fcTmAbs dbinds $
                          substFcTmInTm ev_subst $
                            substFcTyInTm fc_subst fc_tm
  
  -- Unresolved vars
  let unresolved_tyvs = nub (ftyvsOf refined_fc_tm)
                          \\ map rnTyVarToFcTyVar untouchables
  
  -- Substitute unresolved vars "a" with dummy types:
  --   as dummy types, we use the most general polymorphic type (forall a. a)
  unresolved_subst <- do
    new_tyvs <- mapM (freshFcTyVar . kindOf) unresolved_tyvs
    let new_tys = map (\a -> FcTyAbs a $ FcTyVar a) new_tyvs
    return $ foldMap (uncurry (|->)) $ zipExact unresolved_tyvs new_tys
  
  -- Generate the resulting System F term
  return $ substFcTyInTm unresolved_subst refined_fc_tm
  
  where
    (as,cs,ty) = destructPolyTy poly_ty
    fc_as      = map rnTyVarToFcTyVar (labelOf as)

-- | Convert a source type substitution to a System F type substitution
elabHsTySubst :: HsTySubst -> TcM FcTySubst
elabHsTySubst = mapSubM (return . rnTyVarToFcTyVar) elabMonoTy

-- * Type Inference With Constraint Simplification
-- ------------------------------------------------------------------------------

elabTermSimpl :: ProgramTheory -> RnTerm -> TcM (RnPolyTy, FcTerm)
elabTermSimpl theory tm = do
  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  -- Simplify as much as you can
  ty_subst <- unify mempty $ wanted_eqs -- Solve the needed equalities first

  let refined_wanted_ccs = substInSimpleProgramTheory ty_subst wanted_ccs       -- refine the wanted class constraints
  let refined_mono_ty    = substInMonoTy              ty_subst mono_ty          -- refine the monotype
  refined_fc_tm <- elabHsTySubst ty_subst >>= return . flip substFcTyInTm fc_tm -- refine the term

  let untouchables = nub (ftyvsOf refined_mono_ty)

  (residual_cs, ev_subst) <- entailDetTcM untouchables theory refined_wanted_ccs
  -- (residual_cs, ev_subst) <- rightEntailsRec untouchables theory refined_wanted_ccs
  -- GEORGE: Define and use constraint simplification here

-- entailDetTcM :: [RnTyVar] -> ProgramTheory -> ProgramTheory -> TcM (ProgramTheory, FcTmSubst)

  -- Generalize the type
  let new_mono_ty = refined_mono_ty
  let new_cs      = map dropLabel (snocListToList residual_cs) -- refined_wanted_ccs) -- residual_cs)
  let new_as      = untouchables
  let gen_ty      = constructPolyTy (map (\a -> a :| kindOf a) new_as, new_cs, new_mono_ty)

  -- Elaborate the term
  let fc_as = map rnTyVarToFcTyVar new_as
  dbinds   <- annClsCsToTmBinds residual_cs -- refined_wanted_ccs --residual_cs
  let full_fc_tm = fcTmTyAbs fc_as $
                     fcTmAbs dbinds $
                       substFcTmInTm ev_subst $
                         refined_fc_tm

  return (gen_ty, full_fc_tm)

-- * Program Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a program
elabProgram :: FullTheory -> RnProgram
            -> TcM ( FcProgram       {- Elaborated program       -}
                   , RnPolyTy        {- Term type (MonoTy?)      -}
                   , FullTheory )    {- Final program theory     -}
-- ^ Elaborate the program expression
elabProgram theory (PgmExp tm) = do
  (ty, fc_tm) <- elabTermSimpl (ftDropSuper theory) tm
  return (FcPgmTerm fc_tm, ty, theory) -- GEORGE: You should actually return the ones we have accumulated.

-- ^ Elaborate a class declaration
elabProgram theory (PgmCls cls_decl pgm) = do
  (fc_data_decl, fc_val_bind, fc_sc_proj, ext_theory, ext_ty_env)  <- elabClsDecl cls_decl
  (fc_pgm, ty, final_theory) <- setTcCtxTmM ext_ty_env (elabProgram (theory `ftExtendSuper` ext_theory) pgm)
  let fc_program = FcPgmDataDecl fc_data_decl (FcPgmValDecl fc_val_bind (foldl (flip FcPgmValDecl) fc_pgm fc_sc_proj))
  return (fc_program, ty, final_theory)

-- ^ Elaborate a class instance
elabProgram theory (PgmInst ins_decl pgm) = do
  (fc_val_bind, ext_theory) <- elabInsDecl theory ins_decl
  (fc_pgm, ty, final_theory) <- elabProgram ext_theory pgm
  let fc_program = FcPgmValDecl fc_val_bind fc_pgm
  return (fc_program, ty, final_theory)

-- ^ Elaborate a datatype declaration
elabProgram theory (PgmData data_decl pgm) = do
  fc_data_decl <- elabDataDecl data_decl
  (fc_pgm, ty, final_theory) <- elabProgram theory pgm
  let fc_program = FcPgmDataDecl fc_data_decl fc_pgm
  return (fc_program, ty, final_theory)

-- ^ Elaborate a function declaration
elabProgram theory (PgmFunc func_decl pgm) = do
  (fc_val_bind, ext_ty_env) <- elabFuncDecl theory func_decl
  (fc_pgm, ty, final_theory) <- setTcCtxTmM ext_ty_env $ elabProgram theory pgm
  let fc_program = FcPgmValDecl fc_val_bind fc_pgm
  return (fc_program, ty, final_theory)

-- * Invoke the complete type checker
-- ------------------------------------------------------------------------------

hsElaborate :: RnEnv -> UniqueSupply -> RnProgram
            -> (Either String ((((FcProgram, RnPolyTy, FullTheory), (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)), UniqueSupply), TcEnv),
                Trace)
hsElaborate rn_gbl_env us pgm = runWriter
                              $ runExceptT
                              $ flip runStateT  tc_init_gbl_env -- Empty when you start
                              $ flip runReaderT tc_init_ctx
                              $ flip runUniqueSupplyT us
                              $ do { buildInitTcEnv pgm rn_gbl_env -- Create the actual global environment
                                   ; result <- elabProgram tc_init_theory pgm
                                   ; assocs <- buildInitFcAssocs
                                   ; return (result, assocs) }
  where
    tc_init_theory  = FT mempty mempty mempty
    tc_init_ctx     = mempty
    tc_init_gbl_env = TcEnv mempty mempty mempty
