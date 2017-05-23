{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Frontend.HsRenamer (RnEnv(..), hsRename) where

import Frontend.HsTypes
import Backend.FcTypes

import Utils.Unique
import Utils.Var
import Utils.Kind
import Utils.AssocList
import Utils.Ctx
import Utils.PrettyPrint
import Utils.Utils
import Utils.Annotated
import Utils.FreeVars
import Utils.Trace

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.List (nub)
import Control.Arrow (second)

-- * Renaming monad
-- ------------------------------------------------------------------------------

data RnEnv = RnEnv { rn_env_cls_info :: AssocList PsClass   RnClsInfo
                   , rn_env_dc_info  :: AssocList PsDataCon HsDataConInfo
                   , rn_env_tc_info  :: AssocList PsTyCon   HsTyConInfo   }

instance PrettyPrint RnEnv where
  ppr (RnEnv cls_infos dc_infos tc_infos)
    = braces $ vcat $ punctuate comma
    [ text "rn_env_cls_info" <+> colon <+> ppr cls_infos
    , text "rn_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "rn_env_tc_info"  <+> colon <+> ppr tc_infos
    ]
  needsParens _ = False

-- | The renaming context maps parsed term and type variables to renamed term
-- and type variables, respectively.
type RnCtx = Ctx PsTmVar RnTmVar PsTyVar RnTyVar

type RnM = UniqueSupplyT (ReaderT RnCtx (StateT RnEnv (ExceptT String (Writer Trace))))

-- * Basic Monadic Setters and Getters
-- ------------------------------------------------------------------------------

-- | Get all renamed class names from the state
getClsInfoRnM :: RnM (AssocList PsClass RnClsInfo)
getClsInfoRnM = rn_env_cls_info <$> get

-- | Get all renamed datacon names from the state
getDataConInfoRnM :: RnM (AssocList PsDataCon HsDataConInfo)
getDataConInfoRnM = rn_env_dc_info <$> get

-- | Get all renamed tycon names from the state
getTyConInfoRnM :: RnM (AssocList PsTyCon HsTyConInfo)
getTyConInfoRnM = rn_env_tc_info <$> get

-- | Lookup the info of a class
lookupClsInfoRnM :: PsClass -> RnM RnClsInfo
lookupClsInfoRnM cls = getClsInfoRnM >>= \cls_infos ->
  case lookupInAssocList cls cls_infos of
    Just cls_info -> return cls_info
    Nothing       -> throwErrorRnM (text "Class name" <+> ppr cls <+> text "unbound")

-- | Lookup the info of a data constructor
lookupDataConInfoRnM :: PsDataCon -> RnM HsDataConInfo
lookupDataConInfoRnM dc = getDataConInfoRnM >>= \dc_infos ->
  case lookupInAssocList dc dc_infos of
    Just dc_info -> return dc_info
    Nothing      -> throwErrorRnM (text "DataCon name" <+> ppr dc <+> text "unbound")

-- | Lookup the info of a type constructor
lookupTyConInfoRnM :: PsTyCon -> RnM HsTyConInfo
lookupTyConInfoRnM tc = getTyConInfoRnM >>= \tc_infos ->
  case lookupInAssocList tc tc_infos of
    Just tc_info -> return tc_info
    Nothing      -> throwErrorRnM (text "TyCon name" <+> ppr tc <+> text "unbound")

-- | Add a renamed class name to the state
addClsInfoRnM :: PsClass -> RnClsInfo -> RnM ()
addClsInfoRnM cls info = modify $ \s ->
  s { rn_env_cls_info = extendAssocList cls info (rn_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoRnM :: PsDataCon -> HsDataConInfo -> RnM ()
addDataConInfoRnM dc info = modify $ \s ->
  s { rn_env_dc_info = extendAssocList dc info (rn_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoRnM :: PsTyCon -> HsTyConInfo -> RnM ()
addTyConInfoRnM tc info = modify $ \s ->
  s { rn_env_tc_info = extendAssocList tc info (rn_env_tc_info s) }

-- | Assign a unique to a plain symbol
rnSym :: MonadUnique m => Sym -> m Name
rnSym s = getUniqueM >>= return . mkName s

-- | Rename a method name. It has to be unbound
rnMethodName :: PsTmVar -> RnM RnTmVar
rnMethodName x = ask >>= \ctx -> case lookupTmVarCtx ctx x of
  Just {} -> throwErrorRnM (text "Method name" <+> ppr x <+> text "already bound")
  Nothing -> rnTmVar x

-- | Lookup an already-bound method name
lookupMethodName :: PsTmVar -> RnM RnTmVar
lookupMethodName x = ask >>= \ctx -> case lookupTmVarCtx ctx x of
  Just rnx -> return rnx
  Nothing  -> throwErrorRnM (text "Method name" <+> ppr x <+> text "unbound")

-- * Rename Types
-- ------------------------------------------------------------------------------

-- | Rename a type variable
rnTyVar :: PsTyVarWithKind -> RnM RnTyVar
rnTyVar (a :| kind) = flip mkRnTyVar kind <$> rnSym (symOf a)

-- | Rename a type pattern and collect the bound variables
rnTyPat :: PsTyPat -> RnM (RnTyPat, [RnTyVar])
rnTyPat = liftM (second nub) . go
  where
    go :: PsTyPat -> RnM (RnTyPat, [RnTyVar])
    go (HsTyConPat tc) = do
      rntc <- lookupTyCon tc
      return (HsTyConPat rntc, [])
    go (HsTyAppPat ty1 ty2) = do
      (rnty1, bv1) <- go ty1
      (rnty2, bv2) <- go ty2
      return (HsTyAppPat rnty1 rnty2, bv1 ++ bv2)
    go (HsTyVarPat (a :| k)) = do
      rna <- lookupTyVarM a
      unless (kindOf rna == k) $
        throwErrorRnM (text "rnTyPat:" <+> text "Inconsistent kind assignment")
      return (HsTyVarPat (rna :| kindOf rna), [rna])

-- | Rename a monotype
rnMonoTy :: PsMonoTy -> RnM RnMonoTy
rnMonoTy (TyCon tc)      = TyCon <$> lookupTyCon tc
rnMonoTy (TyApp ty1 ty2) = TyApp <$> rnMonoTy ty1 <*> rnMonoTy ty2
rnMonoTy (TyVar psa)     = TyVar <$> lookupTyVarM psa

-- | Rename a qualified type
rnQualTy :: PsQualTy -> RnM RnQualTy
rnQualTy (QMono ty)    = QMono <$> rnMonoTy ty
rnQualTy (QQual ct ty) = QQual <$> rnCtr ct <*> rnQualTy ty

-- | Rename a constraint
rnCtr :: PsCtr -> RnM RnCtr
rnCtr (CtrClsCt cls_ct) = CtrClsCt <$> rnClsCt cls_ct
rnCtr (CtrImpl c1 c2)   = CtrImpl <$> (rnCtr c1) <*> (rnCtr c2)
rnCtr (CtrAbs a ct)     = do
  rna  <- rnTyVar a
  rnct <- extendCtxTyM (labelOf a) rna (rnCtr ct)
  return (CtrAbs (rna :| kindOf rna) rnct)

-- | Rename a class constraint
rnClsCt :: PsClsCt -> RnM RnClsCt
rnClsCt (ClsCt cls ty) = ClsCt <$> rnClass cls <*> rnMonoTy ty

-- | Rename a class name
rnClass :: PsClass -> RnM RnClass
rnClass cls = do
  cls_infos <- getClsInfoRnM
  case lookupInAssocList cls cls_infos of
    Just cls_info -> return (rn_cls_class cls_info)
    Nothing       -> throwErrorRnM (text "Class name" <+> ppr cls <+> text "unbound")

-- | Rename a polytype
rnPolyTy :: PsPolyTy -> RnM RnPolyTy
rnPolyTy (PQual ty)   = PQual <$> rnQualTy ty
rnPolyTy (PPoly a ty) = do
  rna  <- rnTyVar a
  rnty <- extendCtxTyM (labelOf a) rna (rnPolyTy ty)
  return (PPoly (rna :| kindOf rna) rnty)

-- * Rename Terms
-- ------------------------------------------------------------------------------

-- | Rename a term variable
rnTmVar :: PsTmVar -> RnM RnTmVar
rnTmVar psx = mkRnTmVar <$> rnSym (symOf psx)

-- | Rename a term
rnTerm :: PsTerm -> RnM RnTerm
rnTerm (TmVar x)          = TmVar <$> lookupTmVarM x
rnTerm (TmCon dc)         = TmCon <$> lookupDataCon dc
rnTerm (TmAbs psx pstm)   = do
  rnx  <- rnTmVar psx
  rntm <- extendCtxTmM psx rnx (rnTerm pstm)
  return (TmAbs rnx rntm)
rnTerm (TmApp tm1 tm2)    = TmApp <$> rnTerm tm1 <*> rnTerm tm2
rnTerm (TmLet x tm1 tm2)  = do
  rnx   <- rnTmVar x
  rntm1 <- extendCtxTmM x rnx (rnTerm tm1)
  rntm2 <- extendCtxTmM x rnx (rnTerm tm2)
  return (TmLet rnx rntm1 rntm2)
rnTerm (TmCase scr alts)  = TmCase <$> rnTerm scr <*> mapM rnAlt alts

-- | Rename a case alternative
rnAlt :: PsAlt -> RnM RnAlt
rnAlt (HsAlt (HsPat dc xs) tm) = do
  rndc <- lookupDataCon dc
  rnxs <- mapM rnTmVar xs
  let binds = zipExact xs rnxs
  rntm <- extendTmVars binds (rnTerm tm)
  return (HsAlt (HsPat rndc rnxs) rntm)

-- | Rename a type constructor
lookupTyCon :: PsTyCon -> RnM RnTyCon
lookupTyCon tc = hs_tc_ty_con <$> lookupTyConInfoRnM tc

-- | Rename a data constructor
lookupDataCon :: PsDataCon -> RnM RnDataCon
lookupDataCon dc = hs_dc_data_con <$> lookupDataConInfoRnM dc

-- GEORGE: Make this a separate function in Utils.Ctx?
extendTmVars :: [(PsTmVar, RnTmVar)] -> RnM a -> RnM a
extendTmVars binds m = extendCtxTmsM xs xs' m
  where (xs,xs') = unzip binds

-- GEORGE: Make this a separate function in Utils.Ctx?
extendTyVars :: [(PsTyVar, RnTyVar)] -> RnM a -> RnM a
extendTyVars binds m = extendCtxTysM as as' m
  where (as,as') = unzip binds

-- * Rename Programs and Declarations
-- ------------------------------------------------------------------------------

-- | Rename a class declaration
-- GEORGE: It does not return the environment extension, rather the extended environment.
rnClsDecl :: PsClsDecl -> RnM (RnClsDecl, RnCtx)
rnClsDecl (ClsD cs cls a method method_ty) = do
  -- Rename the class name
  rn_cls <- do
    cls_infos <- getClsInfoRnM
    case lookupInAssocList cls cls_infos of
      Just {} -> throwErrorRnM (text "Class" <+> ppr cls <+> text "already defined")
      Nothing -> Class <$> rnSym (symOf cls)

  -- Rename the method name
  rn_method <- rnMethodName method

  -- Store the class info in the global environment
  addClsInfoRnM cls (RnClsInfo rn_cls rn_method)

  -- Rename the type argument
  rn_a <- rnTyVar a

  -- Rename the superclass constraints
  rn_cs <- extendCtxTyM (labelOf a) rn_a (mapM rnCtr cs)

  -- Rename the method type
  rn_method_ty <- extendCtxTyM (labelOf a) rn_a (rnPolyTy method_ty)

  -- Get the current typing environment (so that we can extend it with the method binding)
  rn_ctx <- ask

  return ( ClsD rn_cs rn_cls (rn_a |: kindOf rn_a) rn_method rn_method_ty
         , extendCtxTm rn_ctx method rn_method )

-- | Rename an instance declaration
rnInsDecl :: PsInsDecl -> RnM RnInsDecl
rnInsDecl (InsD cs cls_name ty_pat method_name method_tm) = do
  rn_cls_name     <- rnClass cls_name                        -- rename the class name

  tyvars <- mapM rnTyVar (ftyvsOf ty_pat) -- collect and rename all bound variables

  (rn_ty_pat, bv) <- extendKindedVarsCtxM tyvars (rnTyPat ty_pat) -- rename the type pattern
  rn_cs           <- extendKindedVarsCtxM bv (mapM rnCtr cs)  -- rename the instance context
  rn_method_name  <- lookupMethodName method_name             -- rename the method name

  -- Ensure the method name is for the class we are checking
  expected_method_name <- lookupClassMethodName cls_name
  unless (rn_method_name == expected_method_name) $
    throwErrorRnM (ppr method_name <+> text "does not belong to class" <+> ppr cls_name)

  rn_method_tm    <- rnTerm method_tm                        -- rename the method implementation
  return (InsD rn_cs rn_cls_name rn_ty_pat rn_method_name rn_method_tm)

extendKindedVarsCtxM :: [RnTyVar] -> RnM a -> RnM a
extendKindedVarsCtxM []     m = m
extendKindedVarsCtxM (a:as) m = extendCtxTyM (rnTyVarToPsTyVar a) a (extendKindedVarsCtxM as m)

-- | Lookup the name of the method of a particular class
lookupClassMethodName :: PsClass -> RnM RnTmVar
lookupClassMethodName cls = rn_cls_method <$> lookupClsInfoRnM cls

-- | Rename a datatype declaration
rnDataDecl :: PsDataDecl -> RnM RnDataDecl
rnDataDecl (DataD tc as dcs) = do
  -- Rename the type constructor
  rntc <- do
    tc_infos <- getTyConInfoRnM
    case lookupInAssocList tc tc_infos of
      Just {} -> throwErrorRnM (text "TyCon" <+> ppr tc <+> text "already defined")
      Nothing -> HsTC <$> rnSym (symOf tc)

  -- Rename the universal type variables
  unless (distinct as) $
    throwErrorRnM (text "TyCon" <+> ppr tc <+> text "has non-linear parameters")
  rnas <- mapM rnTyVar as

  -- Store the TyCon info in the global environment
  addTyConInfoRnM tc $ HsTCInfo rntc rnas (FcTC (nameOf rntc))

  -- Rename the data constructors
  let binds = zipExact (map labelOf as) rnas
  rndcs <- forM dcs $ \(dc, tys) -> do
    -- Rename the data constructor
    rndc <- do
      dc_infos <- getDataConInfoRnM
      case lookupInAssocList dc dc_infos of
        Just {} -> throwErrorRnM (text "DataCon" <+> ppr dc <+> text "already defined")
        Nothing -> HsDC <$> rnSym (symOf dc)

    -- Rename the data constructor's type arguments
    rntys <- mapM (extendTyVars binds . rnMonoTy) tys

    -- Store the DataCon info in the global environment
    addDataConInfoRnM dc $ HsDCInfo rndc rnas rntc (map monoTyToPolyTy rntys) (FcDC (nameOf rndc))

    return (rndc, rntys)

  return (DataD rntc (rnas |: map kindOf rnas) rndcs)

-- | Rename a program
rnProgram :: PsProgram -> RnM (RnProgram, RnCtx)
rnProgram (PgmExp tm) = do
  rn_tm  <- rnTerm tm
  rn_ctx <- ask
  return (PgmExp rn_tm, rn_ctx)
rnProgram (PgmCls cls_decl pgm) = do
  (rn_cls_decl, ext_ctx) <- rnClsDecl cls_decl
  (rn_pgm, rn_ctx)       <- local (\_ -> ext_ctx) $ rnProgram pgm
  return (PgmCls rn_cls_decl rn_pgm, rn_ctx)
rnProgram (PgmInst ins_decl pgm) = do
  rn_ins_decl      <- rnInsDecl ins_decl
  (rn_pgm, rn_ctx) <- rnProgram pgm
  return (PgmInst rn_ins_decl rn_pgm, rn_ctx)
rnProgram (PgmData data_decl pgm) = do
  rn_data_decl <- rnDataDecl data_decl
  (rn_pgm, rn_ctx) <- rnProgram pgm
  return (PgmData rn_data_decl rn_pgm, rn_ctx)

-- * Invoke the complete renamer
-- ------------------------------------------------------------------------------

hsRename :: UniqueSupply -> PsProgram
         -> (Either String (((RnProgram, RnCtx), UniqueSupply), RnEnv), Trace)
hsRename us pgm = runWriter
                $ runExceptT
                $ flip runStateT  rn_init_gbl_env
                $ flip runReaderT rn_init_ctx
                $ flip runUniqueSupplyT us
                $ rnProgram pgm
  where
    rn_init_ctx     = mempty
    rn_init_gbl_env = RnEnv { rn_env_cls_info = mempty
                            , rn_env_dc_info  = mempty
                            , rn_env_tc_info  = extendAssocList psArrowTyCon arrowTyConInfo mempty
                            }

-- | Throw an error
throwErrorRnM :: Doc -> RnM a
throwErrorRnM d = throwError (renderError d)
