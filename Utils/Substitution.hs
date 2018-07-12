{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.Substitution where

import Frontend.HsTypes
import Backend.FcTypes

import Utils.Var
import Utils.Kind
import Utils.Annotated
import Utils.Unique
import Utils.Utils
import Utils.PrettyPrint

import Control.Monad (liftM2)

-- * The SubstVar Class
-- ------------------------------------------------------------------------------

class SubstVar v t x | v x -> t where -- The FD means that we can not use the class for renaming substitutions.
  substVar :: v -> t -> x -> x

instance SubstVar v t x => SubstVar v t [x] where
  substVar v t xs = map (substVar v t) xs

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
    CtrClsCt ct     -> CtrClsCt (substVar a ty ct)
    CtrImpl ct1 ct2 -> CtrImpl (substVar a ty ct1) (substVar a ty ct2)
    CtrAbs (b :| k) ct
      | a == b      -> error "substTyVarInCtr: Shadowing"
      | otherwise   -> CtrAbs (b :| k) (substVar a ty ct)

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
instance SubstVar FcTyVar FcType FcTerm where
  substVar a aty = \case
    FcTmVar x            -> FcTmVar x
    FcTmAbs x ty tm      -> FcTmAbs x (substVar a aty ty) (substVar a aty tm)
    FcTmApp tm1 tm2      -> FcTmApp (substVar a aty tm1) (substVar a aty tm2)
    FcTmTyAbs b tm
      | a == b           -> error "substFcTyVarInTm: Shadowing (tyabs)"
      | otherwise        -> FcTmTyAbs b (substVar a aty tm)
    FcTmTyApp tm ty      -> FcTmTyApp (substVar a aty tm) (substVar a aty ty)
    FcTmDataCon dc       -> FcTmDataCon dc
    FcTmLet x ty tm1 tm2 -> FcTmLet x (substVar a aty ty) (substVar a aty tm1) (substVar a aty tm2)
    FcTmCase tm cs       -> FcTmCase (substVar a aty tm) (map (substVar a aty) cs)

-- | Substitute a type variable for a type in a case alternative
instance SubstVar FcTyVar FcType FcAlt where
  substVar a ty (FcAlt p tm) = FcAlt p (substVar a ty tm)
  -- GEORGE: Now the patterns do not bind type variables so we don't have to check for shadowing here.

-- * Target Language SubstVar Instances (Term Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a term variable for a term in a term
instance SubstVar FcTmVar FcTerm FcTerm where
  substVar x xtm = \case
    FcTmVar y
      | x == y      -> xtm
      | otherwise   -> FcTmVar y
    FcTmAbs y ty tm
      | x == y      -> error "substFcTmVarInTm: Shadowing (tmabs)"
      | otherwise   -> FcTmAbs y ty (substVar x xtm tm)
    FcTmApp tm1 tm2 -> FcTmApp (substVar x xtm tm1) (substVar x xtm tm2)

    FcTmTyAbs a tm  -> FcTmTyAbs a (substVar x xtm tm)
    FcTmTyApp tm ty -> FcTmTyApp (substVar x xtm tm) ty
    FcTmDataCon dc  -> FcTmDataCon dc
    FcTmLet y ty tm1 tm2
      | x == y      -> error "substFcTmVarInTm: Shadowing (let)"
      | otherwise   -> FcTmLet y ty (substVar x xtm tm1) (substVar x xtm tm2)
    FcTmCase tm cs  -> FcTmCase (substVar x xtm tm) (map (substVar x xtm) cs)

-- | Substitute a term variable for a term in a case alternative
instance SubstVar FcTmVar FcTerm FcAlt where
  substVar x xtm (FcAlt (FcConPat dc xs) tm)
    | not (distinct xs) = error "substFcTmVarInAlt: Variables in pattern are not distinct" -- extra redundancy for safety
    | any (==x) xs      = error "substFcTmVarInAlt: Shadowing"
    | otherwise         = FcAlt (FcConPat dc xs) (substVar x xtm tm)

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
substFcTyInTm :: FcTySubst -> FcTerm -> FcTerm
substFcTyInTm = sub_rec

-- | Apply a type substitution to a case alternative
substFcTyInAlt :: FcTySubst -> FcAlt -> FcAlt
substFcTyInAlt = sub_rec -- XXX: subst (FcAlt p tm) = FcAlt p (substFcTyInTm subst tm)
  -- GEORGE: Now the patterns do not bind type variables so we don't have to check for shadowing here.

-- * System F Term Substitution
-- ------------------------------------------------------------------------------

type FcTmSubst = Sub FcTmVar FcTerm

-- | Apply a term substitution to a term
substFcTmInTm :: FcTmSubst -> FcTerm -> FcTerm
substFcTmInTm = sub_rec

-- | Apply a term substitution to a case alternative
substFcTmInAlt :: FcTmSubst -> FcAlt -> FcAlt
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

-- | Freshen the (type) binders of a type scheme
instance FreshenLclBndrs RnPolyTy where
  freshenLclBndrs (PQual ty) = return (PQual ty)
  freshenLclBndrs (PPoly (a :| _) ty) = freshRnTyVar (kindOf a) >>= \b ->
    PPoly (b :| kindOf b) <$> freshenLclBndrs (substVar a (TyVar b) ty)

-- | Freshen the (type) binders of a constraint
instance FreshenLclBndrs RnCtr where
  freshenLclBndrs (CtrClsCt ct)        = return (CtrClsCt ct)
  freshenLclBndrs (CtrImpl ct1 ct2)    = CtrImpl <$> freshenLclBndrs ct1 <*> freshenLclBndrs ct2
  freshenLclBndrs (CtrAbs (a :| _) ct) = freshRnTyVar (kindOf a) >>= \b ->
    CtrAbs (b :| kindOf b) <$> freshenLclBndrs (substVar a (TyVar b) ct)

-- | Freshen the (type) binders of a System F type
instance FreshenLclBndrs FcType where
  freshenLclBndrs (FcTyVar a)       = return (FcTyVar a)
  freshenLclBndrs (FcTyAbs a ty)    = freshFcTyVar (kindOf a) >>= \b ->
    FcTyAbs b <$> freshenLclBndrs (substVar a (FcTyVar b) ty)
  freshenLclBndrs (FcTyApp ty1 ty2) = FcTyApp <$> freshenLclBndrs ty1 <*> freshenLclBndrs ty2
  freshenLclBndrs (FcTyCon tc)      = return (FcTyCon tc)

-- | Freshen the (type + term) binders of a System F term
instance FreshenLclBndrs FcTerm where
  freshenLclBndrs (FcTmAbs x ty tm) = freshFcTmVar >>= \y ->
    FcTmAbs y <$> freshenLclBndrs ty <*> freshenLclBndrs (substVar x (FcTmVar y) tm)
  freshenLclBndrs (FcTmVar x)       = return (FcTmVar x)
  freshenLclBndrs (FcTmApp tm1 tm2) = FcTmApp <$> freshenLclBndrs tm1 <*> freshenLclBndrs tm2
  freshenLclBndrs (FcTmTyAbs a tm)  = freshFcTyVar (kindOf a) >>= \b ->
    FcTmTyAbs b <$> freshenLclBndrs (substVar a (FcTyVar b) tm)
  freshenLclBndrs (FcTmTyApp tm ty) = FcTmTyApp <$> freshenLclBndrs tm <*> freshenLclBndrs ty
  freshenLclBndrs (FcTmDataCon dc)  = return (FcTmDataCon dc)
  freshenLclBndrs (FcTmLet x ty tm1 tm2) = freshFcTmVar >>= \y ->
    FcTmLet y <$> freshenLclBndrs ty
              <*> freshenLclBndrs (substVar x (FcTmVar y) tm1)
              <*> freshenLclBndrs (substVar x (FcTmVar y) tm2)

  freshenLclBndrs (FcTmCase tm cs) = FcTmCase <$> freshenLclBndrs tm <*> mapM freshenLclBndrs cs

-- | Freshen the (type + term) binders of a System F case alternative
instance FreshenLclBndrs FcAlt where
  freshenLclBndrs (FcAlt (FcConPat dc xs) tm) = do
    ys  <- mapM (\_ -> freshFcTmVar) xs
    tm' <- freshenLclBndrs $ foldl (\t (x,y) -> substVar x (FcTmVar y) t) tm (zipExact xs ys)
    return (FcAlt (FcConPat dc ys) tm')
