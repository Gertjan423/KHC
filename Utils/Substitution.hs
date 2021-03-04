{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.Substitution where

import Frontend.HsTypes
import Optimizer.FcTypes

import Utils.Var
import Utils.Kind
import Utils.Annotated
import Utils.Unique
import Utils.Utils
import Utils.PrettyPrint

import Control.Monad (liftM2, replicateM)

-- * The SubstVar Class
-- ------------------------------------------------------------------------------

class SubstVar v t x | v x -> t where -- The FD means that we can not use the class for renaming substitutions.
  substVar :: v -> t -> x -> x

instance SubstVar v t x => SubstVar v t [x] where
  substVar v t xs = map (substVar v t) xs

instance SubstVar v t x => SubstVar [v] [t] x where
  substVar vs ts x = foldr (\(v',t') -> substVar v' t') x (zipExact vs ts)

-- * Source Language SubstVar Instances (Type Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a type variable for a type in a type
instance SubstVar RnTyVar RnMonoTy RnMonoTy where
  substVar a ty = \case
    TyVar b
      | a == b    -> ty
      | otherwise -> TyVar b
    TyCon tc      -> TyCon tc
    TyApp ty1 ty2 -> TyApp (substVar a ty ty1) (substVar a ty ty2)

-- | Substitute a type variable for a type in a class constraint
instance SubstVar RnTyVar RnMonoTy RnClsCt where
  substVar a ty (ClsCt cls mono) = ClsCt cls (substVar a ty mono)

-- | Substitute a type variable for a type in a qualified type
instance SubstVar RnTyVar RnMonoTy RnQualTy where
  substVar a aty = \case
    QMono    ty -> QMono (substVar a aty ty)
    QQual ct ty -> QQual (substVar a aty ct) (substVar a aty ty)

-- | Substitute a type variable for a type in a type scheme
instance SubstVar RnTyVar RnMonoTy RnPolyTy where
  substVar a aty = \case
    PQual ty      -> PQual (substVar a aty ty)
    PPoly (b :| kind) ty
      | a == b    -> error "substTyVarInPolyTy: Shadowing"
      | otherwise -> PPoly (b :| kind) (substVar a aty ty)

-- | Substitute a type variable for a type in a constraint
instance SubstVar RnTyVar RnMonoTy RnCtr where
  substVar a ty = \case
    Ctr as cs ct
      | elem a (map labelOf as) -> error "substTyVarInCtr: Shadowing"
      | otherwise -> Ctr as (map (substVar a ty) cs) (substVar a ty ct)

-- * Target Language SubstVar Instances (Type Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a type variable for a type in a type
instance SubstVar FcTyVar FcType FcType where
  substVar a ty = \case
    FcTyVar b
      | a == b      -> ty
      | otherwise   -> FcTyVar b
    FcTyAbs b ty1
      | a == b      -> error "substFcVarInFcType: Shadowing (tyabs)"
      | otherwise   -> FcTyAbs b (substVar a ty ty1)
    FcTyApp ty1 ty2 -> FcTyApp (substVar a ty ty1) (substVar a ty ty2)
    FcTyCon tc      -> FcTyCon tc

-- | Substitute a type variable for a type in a term
instance SubstVar FcTyVar FcType (FcTerm a) where
  substVar a aty = \case
    -- Opt
    FcOptTmVar x            -> FcOptTmVar x
    FcOptTmPrim tm          -> FcOptTmPrim tm
    FcOptTmAbs ab           -> FcOptTmAbs (substVar a aty ab)
    FcOptTmApp tm1 tm2      -> FcOptTmApp (substVar a aty tm1) (substVar a aty tm2)
    FcOptTmTyAbs b tm
      | a == b           -> error "substFcTyVarInTm: Shadowing (tyabs)"
      | otherwise        -> FcOptTmTyAbs b (substVar a aty tm)
    FcOptTmTyApp tm ty   -> FcOptTmTyApp (substVar a aty tm) (substVar a aty ty)
    FcOptTmDataCon dc    -> FcOptTmDataCon dc
    -- Pre
    FcPreTmVarApp x at  -> FcPreTmVarApp x (substVar a aty at)
    FcPreTmDCApp dc at  -> FcPreTmDCApp dc (substVar a aty at)
    FcPreTmPApp  op at  -> FcPreTmPApp  op (substVar a aty at)
    FcPreTmTyAbs bs tm
      | a `elem` bs      -> error "substFcTyVarInTm: Shadowing (tyabs)"
      | otherwise        -> FcPreTmTyAbs bs (substVar a aty tm)
    -- Universal
    FcTmLet bind tm      -> FcTmLet (substVar a aty bind) (substVar a aty tm)
    FcTmCase tm alts     -> FcTmCase (substVar a aty tm) (substVar a aty alts)

instance SubstVar FcTyVar FcType (FcBind a) where
  substVar a aty = \case
    FcOptBind x ty tm -> FcOptBind x (substVar a aty ty) (substVar a aty tm)
    FcPreBind x ty ab -> FcPreBind x (substVar a aty ty) (substVar a aty ab)

instance SubstVar FcTyVar FcType (FcAbs a) where
  substVar a aty = \case
    FcOptAbs x  ty  tm -> FcOptAbs x  (substVar a aty ty ) (substVar a aty tm)
    FcPreAbs xs tys tm -> FcPreAbs xs (substVar a aty tys) (substVar a aty tm)

instance SubstVar FcTyVar FcType FcAtom where
  substVar a aty = \case
    FcAtVar x   -> FcAtVar x
    FcAtLit l   -> FcAtLit l
    FcAtType ty -> FcAtType (substVar a aty ty)

-- | Substitute a type variable for a type in a case alternative
instance SubstVar FcTyVar FcType (FcAlts a) where
  substVar a ty = \case
    FcAAlts alts -> FcAAlts (substVar a ty alts)
    FcPAlts alts -> FcPAlts (substVar a ty alts)
  -- GEORGE: Now the patterns do not bind type variables so we don't have to check for shadowing here.

instance SubstVar FcTyVar FcType (FcAAlt a) where
  substVar a ty (FcAAlt pat tm) = FcAAlt pat (substVar a ty tm)

instance SubstVar FcTyVar FcType (FcPAlt a) where
  substVar a ty (FcPAlt lit tm) = FcPAlt lit (substVar a ty tm)

-- * Target Language SubstVar Instances (Term Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a term variable for a term in a term
instance SubstVar FcTmVar (FcTerm a) (FcTerm a) where  
  substVar x xtm
    | fcPhase == Opt = \case
      -- Opt
      FcOptTmVar y
        | x == y         -> xtm
        | otherwise      -> FcOptTmVar y
      FcOptTmPrim tm     -> FcOptTmPrim tm
      FcOptTmAbs ab      -> FcOptTmAbs (substVar x xtm ab)
      FcOptTmApp tm1 tm2 -> FcOptTmApp (substVar x xtm tm1) (substVar x xtm tm2)
      FcOptTmTyAbs a tm  -> FcOptTmTyAbs a (substVar x xtm tm)
      FcOptTmTyApp tm ty -> FcOptTmTyApp (substVar x xtm tm) ty
      FcOptTmDataCon dc  -> FcOptTmDataCon dc
      -- Pre
      -- FcPreTmVarApp x ats -> FcPreTmVarApp x ats
      -- FcPreTmDCApp dc ats -> FcPreTmDCApp dc ats
      -- FcPreTmPApp  op ats -> FcPreTmPApp  op ats
      -- FcPreTmTyAbs as tm -> FcPreTmTyAbs as (substVar x xtm tm)
      -- Univ
      FcTmLet bind tm  -> FcTmLet (substVar x xtm bind) (substVar x xtm tm)
      FcTmCase tm alts -> FcTmCase (substVar x xtm tm) (substVar x xtm alts)

-- | Substitute a term variable for a term in a value binding
instance SubstVar FcTmVar (FcTerm Opt) (FcBind Opt) where
  substVar x xtm (FcOptBind y ty tm)
    | x == y    = error "substFcTmVarInTm: Shadowing (let)"
    | otherwise = FcOptBind y ty (substVar x xtm tm)
  -- substVar x xtm (FcPreBind y ty ab)
  --   | x == y    = error "substFcTmVarInTm: Shadowing (let)"
  --   | otherwise = FcPreBind y ty (substVar x xtm ab)

instance SubstVar FcTmVar (FcTerm Opt) (FcAbs Opt) where
  substVar x xtm (FcOptAbs y ty tm)
    | x == y      = error "substFcTmVarInTm: Shadowing (tmabs)"
    | otherwise   = FcOptAbs y ty (substVar x xtm tm)
  -- substVar x xtm (FcPreAbs ys tys tm)
  --   | x `elem` ys = error "substFcTmVarInTm: Shadowing (letabs)"
  --   | otherwise   = FcPreAbs ys tys (substVar x xtm tm)

-- | Substitute a term variable for a term in a case alternative
instance SubstVar FcTmVar (FcTerm Opt) (FcAlts Opt) where
  substVar x xtm (FcAAlts alts) = FcAAlts (substVar x xtm alts)
  substVar x xtm (FcPAlts alts) = FcPAlts (substVar x xtm alts)

instance SubstVar FcTmVar (FcTerm Opt) (FcAAlt Opt) where
  substVar x xtm (FcAAlt (FcConPat dc xs) tm)
    | not (distinct xs) = error "substFcTmVarInAlt: Variables in pattern are not distinct" -- extra redundancy for safety
    | any (==x) xs      = error "substFcTmVarInAlt: Shadowing"
    | otherwise         = FcAAlt (FcConPat dc xs) (substVar x xtm tm)    

instance SubstVar FcTmVar (FcTerm Opt) (FcPAlt Opt) where
  substVar x xtm (FcPAlt lit tm) = FcPAlt lit (substVar x xtm tm)

-- | Substitute one variable for another in a term (preprocessed syntax disallows variables as terms)
instance SubstVar FcTmVar FcTmVar (FcTerm Pre) where
  substVar x y 
    | fcPhase == Pre = \case
      FcPreTmVarApp z ats 
        | x == z    -> FcPreTmVarApp y (substVar x y ats)
        | otherwise -> FcPreTmVarApp z (substVar x y ats)
      FcPreTmDCApp dc ats -> FcPreTmDCApp dc (substVar x y ats)
      FcPreTmPApp  op ats -> FcPreTmPApp  op (substVar x y ats)
      FcPreTmTyAbs as tm  -> FcPreTmTyAbs as (substVar x y tm)
      FcTmLet bind tm -> FcTmLet (substVar x y bind) (substVar x y tm)
      FcTmCase tm alts -> FcTmCase (substVar x y tm) (substVar x y alts)
    | otherwise = undefined

instance SubstVar FcTmVar FcTmVar FcAtom where
  substVar x y (FcAtVar z) 
    | x == z = FcAtVar y
  substVar x y at = at

instance SubstVar FcTmVar FcTmVar (FcBind Pre) where
  substVar x y (FcPreBind z ty ab)
    | x == z    = error "substFcTmVarInTm: Shadowing (let)"
    | otherwise = FcPreBind z ty (substVar x y ab)

instance SubstVar FcTmVar FcTmVar (FcAbs Pre) where
  substVar x y (FcPreAbs zs tys tm)
    | x `elem` zs = error "substFcTmVarInTm: Shadowing (letabs)"
    | otherwise   = FcPreAbs zs tys (substVar x y tm)

instance SubstVar FcTmVar FcTmVar (FcAlts Pre) where
  substVar x y (FcAAlts alts) = FcAAlts (substVar x y alts)
  substVar x y (FcPAlts alts) = FcPAlts (substVar x y alts)

instance SubstVar FcTmVar FcTmVar (FcAAlt Pre) where
  substVar x y (FcAAlt (FcConPat dc xs) tm)
    | not (distinct xs) = error "substFcTmVarInAlt: Variables in pattern are not distinct" -- extra redundancy for safety
    | any (==x) xs      = error "substFcTmVarInAlt: Shadowing"
    | otherwise         = FcAAlt (FcConPat dc xs) (substVar x y tm)

instance SubstVar FcTmVar FcTmVar (FcPAlt Pre) where
  substVar x y (FcPAlt lit tm) = FcPAlt lit (substVar x y tm)

-- ------------------------------------------------------------------------------

-- | General structure of substitutions as snoc lists
data Sub x y = SNil | SCons (Sub x y) x y

mapSubM :: Monad m => (x -> m x') -> (y -> m y') -> Sub x y -> m (Sub x' y')
mapSubM _fx _fy SNil          = return SNil
mapSubM  fx  fy (SCons s x y) = do
  s' <- mapSubM fx fy s
  x' <- fx x
  y' <- fy y
  return (SCons s' x' y')

instance (PrettyPrint x, PrettyPrint y) => PrettyPrint (Sub x y) where
  ppr = brackets . sep . punctuate comma. reverse . to_doc_list
    where
      to_doc_list SNil          = []
      to_doc_list (SCons s x y) = (ppr x <+> text "|->" <+> ppr y) : to_doc_list s

  needsParens _ = False

instance Semigroup (Sub x y) where
  (<>) sub SNil          = sub
  (<>) sub (SCons s x y) = SCons (sub <> s) x y

instance Monoid (Sub x y) where
  mempty = SNil
  mconcat = foldl mappend SNil -- foldl since mappend does induction on the second argument

instance Subst (Sub x y) x y where
  (|->) x y = SCons SNil x y

-- | GEORGE: DOCUMENT ME
sub_rec :: SubstVar v t x => Sub v t -> x -> x
sub_rec SNil          t = t
sub_rec (SCons s x y) t = sub_rec s (substVar x y t)

-- * The ApplySubst Class
-- ------------------------------------------------------------------------------

class ApplySubst s t where
  applySubst :: s -> t -> t

instance ApplySubst s t => ApplySubst s [t] where
  applySubst s xs = map (applySubst s) xs

instance SubstVar v t x => ApplySubst (Sub v t) x where
  applySubst = sub_rec

-- * Type Substitution (Source Language)
-- ------------------------------------------------------------------------------

type HsTySubst = Sub RnTyVar RnMonoTy

-- | Build a type substitution from an association list between type variables
buildRnSubst :: [(RnTyVar, RnTyVar)] -> HsTySubst
buildRnSubst = foldl (\s (x,y) -> SCons s x (TyVar y)) SNil

-- | Apply a type substitution to a monotype
substInMonoTy :: HsTySubst -> RnMonoTy -> RnMonoTy
substInMonoTy = sub_rec

-- | Apply a type substitution to a type equality
substInEqCt :: HsTySubst -> EqCt -> EqCt
substInEqCt subst (ty1 :~: ty2) = substInMonoTy subst ty1 :~: substInMonoTy subst ty2

-- | Apply a type substitution to a a list of type equalities
substInEqCs :: HsTySubst -> EqCs -> EqCs
substInEqCs subst = map (substInEqCt subst)

-- | Apply a type substitution to a constraint
substInCtr :: HsTySubst -> RnCtr -> RnCtr
substInCtr = sub_rec

-- | Apply a type substitution to a list of constraints
substInCts :: HsTySubst -> RnCts -> RnCts
substInCts subst = map (substInCtr subst)

-- | Apply a type substitution to a class constraint
substInClsCt :: HsTySubst -> RnClsCt -> RnClsCt
substInClsCt subst (ClsCt cls ty) = ClsCt cls (substInMonoTy subst ty)

-- | Apply a type substitution to a list of class constraints
substInClsCs :: HsTySubst -> RnClsCs -> RnClsCs
substInClsCs subst = map (substInClsCt subst)

-- | Apply a type substitution to a type variable
substInTyVar :: HsTySubst -> RnTyVar -> RnMonoTy
substInTyVar subst tv = substInMonoTy subst (TyVar tv)

-- | Apply a type substitution to a list of type variables
substInTyVars :: HsTySubst -> [RnTyVar] -> [RnMonoTy]
substInTyVars subst = map (substInTyVar subst)

-- | Apply a type substitution to a program theory
substInProgramTheory :: HsTySubst -> ProgramTheory -> ProgramTheory
substInProgramTheory subst = fmap (\(d :| ct) -> (d :| substInCtr subst ct))

-- | Apply a type substitution to a simple program theory
substInSimpleProgramTheory :: HsTySubst -> SimpleProgramTheory -> SimpleProgramTheory
substInSimpleProgramTheory subst = fmap (\(d :| ct) -> (d :| substInClsCt subst ct))

-- | Apply a type substitution to a qualified type
substInQualTy :: HsTySubst -> RnQualTy -> RnQualTy
substInQualTy = sub_rec

-- | Apply a type substitution to a type scheme
substInPolyTy :: HsTySubst -> RnPolyTy -> RnPolyTy
substInPolyTy = sub_rec

-- * System F Type Substitution
-- ------------------------------------------------------------------------------

type FcTySubst = Sub FcTyVar FcType

-- | Apply a type substitution to a type
substFcTyInTy :: FcTySubst -> FcType -> FcType
substFcTyInTy = sub_rec

-- | Apply a type substitution to a term
substFcTyInTm :: FcTySubst -> (FcTerm a) -> (FcTerm a)
substFcTyInTm = sub_rec

-- | Apply a type substitution to a case alternative
substFcTyInAlt :: FcTySubst -> (FcAlts a) -> (FcAlts a)
substFcTyInAlt = sub_rec -- XXX: subst (FcAlt p tm) = FcAlt p (substFcTyInTm subst tm)
  -- GEORGE: Now the patterns do not bind type variables so we don't have to check for shadowing here.

-- * System F Term Substitution
-- ------------------------------------------------------------------------------

type (FcTmSubst a) = Sub FcTmVar (FcTerm a)

-- | Apply a term substitution to a term
substFcTmInTm :: (FcTmMarker a) => (FcTmSubst a) -> (FcTerm a) -> (FcTerm a)
substFcTmInTm = sub_rec

-- | Apply a term substitution to a case alternative
substFcTmInAlt :: (FcTmMarker a) => (FcTmSubst a) -> (FcAlts a) -> (FcAlts a)
substFcTmInAlt = sub_rec

-- * The Subst class
-- ------------------------------------------------------------------------------

class Monoid s => Subst s dom img | s -> dom img, dom img -> s where
  (|->)   :: dom -> img -> s

-- * Alpha-equality on System F Types
-- ------------------------------------------------------------------------------

-- | Alpha equality on types
alphaEqFcTypes :: MonadUnique m => FcType -> FcType -> m Bool
alphaEqFcTypes (FcTyVar a)       (FcTyVar b)       = return (a == b)
alphaEqFcTypes (FcTyAbs a ty1) (FcTyAbs b ty2) = do
  -- GEORGE: Do we need to check that the kinds are the same?
  -- Need to go over the implementation at some point soon.
  c <- FcTyVar <$> freshFcTyVar (kindOf a)
  let ty1' = substFcTyInTy (a |-> c) ty1
  let ty2' = substFcTyInTy (b |-> c) ty2
  alphaEqFcTypes ty1' ty2'
alphaEqFcTypes (FcTyApp ty1 ty2) (FcTyApp ty3 ty4) = liftM2 (&&) (alphaEqFcTypes ty1 ty3) (alphaEqFcTypes ty2 ty4)
alphaEqFcTypes (FcTyCon tc1)     (FcTyCon tc2)     = return (tc1 == tc2)

alphaEqFcTypes (FcTyVar {}) _ = return False
alphaEqFcTypes (FcTyAbs {}) _ = return False
alphaEqFcTypes (FcTyApp {}) _ = return False
alphaEqFcTypes (FcTyCon {}) _ = return False

-- * Freshen up all local binders
-- ------------------------------------------------------------------------------

class FreshenLclBndrs a where
  freshenLclBndrs :: MonadUnique m => a -> m a

instance FreshenLclBndrs a => FreshenLclBndrs [a] where
  freshenLclBndrs = mapM freshenLclBndrs

-- | Freshen the (type) binders of a type scheme
instance FreshenLclBndrs RnPolyTy where
  freshenLclBndrs (PQual ty) = return (PQual ty)
  freshenLclBndrs (PPoly (a :| _) ty) = freshRnTyVar (kindOf a) >>= \b ->
    PPoly (b :| kindOf b) <$> freshenLclBndrs (substVar a (TyVar b) ty)

-- | Freshen the (type) binders of a constraint
instance FreshenLclBndrs RnCtr where
  freshenLclBndrs (Ctr []     cs ct) = return (Ctr [] cs ct)
  freshenLclBndrs (Ctr ((a :| _):as) cs ct) = do
    b                <- freshRnTyVar (kindOf a)
    (Ctr bs cs' ct') <- freshenLclBndrs (substVar a (TyVar b) $ Ctr as cs ct)
    return (Ctr ((b :| kindOf b) : bs) cs' ct')

-- | Freshen the (type) binders of a System F type
instance FreshenLclBndrs FcType where
  freshenLclBndrs (FcTyVar a)       = return (FcTyVar a)
  freshenLclBndrs (FcTyAbs a ty)    = freshFcTyVar (kindOf a) >>= \b ->
    FcTyAbs b <$> freshenLclBndrs (substVar a (FcTyVar b) ty)
  freshenLclBndrs (FcTyApp ty1 ty2) = FcTyApp <$> freshenLclBndrs ty1 <*> freshenLclBndrs ty2
  freshenLclBndrs (FcTyCon tc)      = return (FcTyCon tc)

-- | Freshen the (type + term) binders of a System F term
instance (FcTmMarker a) => FreshenLclBndrs (FcTerm a) where
  -- Opt
  freshenLclBndrs (FcOptTmVar x)       = return (FcOptTmVar x)
  freshenLclBndrs (FcOptTmPrim tm)     = return (FcOptTmPrim tm)
  freshenLclBndrs (FcOptTmAbs ab)      = FcOptTmAbs <$> freshenLclBndrs ab
  freshenLclBndrs (FcOptTmApp tm1 tm2) = FcOptTmApp <$> freshenLclBndrs tm1 <*> freshenLclBndrs tm2
  freshenLclBndrs (FcOptTmTyAbs a tm)  = freshFcTyVar (kindOf a) >>= \b ->
    FcOptTmTyAbs b <$> freshenLclBndrs (substVar a (FcTyVar b) tm)
  freshenLclBndrs (FcOptTmTyApp tm ty) = FcOptTmTyApp <$> freshenLclBndrs tm <*> freshenLclBndrs ty
  freshenLclBndrs (FcOptTmDataCon dc)  = return (FcOptTmDataCon dc)
  -- Pre
  freshenLclBndrs (FcPreTmVarApp x ats) = return (FcPreTmVarApp x ats)
  freshenLclBndrs (FcPreTmDCApp dc ats) = return (FcPreTmDCApp dc ats)
  freshenLclBndrs (FcPreTmPApp  op ats) = return (FcPreTmPApp  op ats)
  freshenLclBndrs (FcPreTmTyAbs as tm) = mapM freshFcTyVar (map kindOf as) >>= \bs ->
    FcPreTmTyAbs bs <$> freshenLclBndrs (substVar as (map FcTyVar bs) tm)
  -- Univ
  freshenLclBndrs (FcTmLet (FcOptBind x ty tm1) tm2) = freshFcTmVar >>= \y ->
    FcTmLet <$> (FcOptBind y <$> freshenLclBndrs ty
              <*> freshenLclBndrs (substVar x (FcOptTmVar y) tm1))
              <*> freshenLclBndrs (substVar x (FcOptTmVar y) tm2)
  freshenLclBndrs (FcTmLet (FcPreBind x ty ab) tm)   = freshFcTmVar >>= \y ->
    FcTmLet <$> (FcPreBind y <$> freshenLclBndrs ty
              <*> freshenLclBndrs (substVar x y ab))
              <*> freshenLclBndrs (substVar x y tm) 
  freshenLclBndrs (FcTmCase tm alts) = FcTmCase <$> freshenLclBndrs tm <*> freshenLclBndrs alts

-- Note: FreshenLclBndrs instance for FcBind is absorbed into Let

-- | Freshen the (type + term) binders of a System F lambda abstraction
instance (FcTmMarker a) => FreshenLclBndrs (FcAbs a) where
  freshenLclBndrs (FcOptAbs x  ty  tm) = freshFcTmVar >>= \y ->
    FcOptAbs y  <$> freshenLclBndrs ty  <*> freshenLclBndrs (substVar x (FcOptTmVar y) tm)
  freshenLclBndrs (FcPreAbs xs tys tm) = replicateM (length xs) freshFcTmVar >>= \ys ->
    FcPreAbs ys <$> freshenLclBndrs tys <*> freshenLclBndrs (substVar xs ys tm)

instance (FcTmMarker a) => FreshenLclBndrs (FcAlts a) where
  freshenLclBndrs (FcAAlts alts) = FcAAlts <$> mapM freshenLclBndrs alts
  freshenLclBndrs (FcPAlts alts) = FcPAlts <$> mapM freshenLclBndrs alts

-- | Freshen the (type + term) binders of a System F case alternative
instance FcTmMarker a => FreshenLclBndrs (FcAAlt a) where
  freshenLclBndrs (FcAAlt (FcConPat dc xs) tm) | fcPhase == Opt = do {
      ys  <- mapM (\_ -> freshFcTmVar) xs;
      tm' <- freshenLclBndrs $ substVar xs (map FcOptTmVar ys) tm;
      return (FcAAlt (FcConPat dc ys) tm')}
  freshenLclBndrs (FcAAlt (FcConPat dc xs) tm) | fcPhase == Pre = do {
      ys <- replicateM (length xs) freshFcTmVar;
      tm' <- freshenLclBndrs $ substVar xs ys tm;
      return (FcAAlt (FcConPat dc ys) tm')}

instance (FcTmMarker a) => FreshenLclBndrs (FcPAlt a) where
  freshenLclBndrs (FcPAlt lit tm) = FcPAlt lit <$> (freshenLclBndrs tm)
