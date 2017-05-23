{-# LANGUAGE FunctionalDependencies #-}

module Frontend.Conditions (unambigCtr, termCond, ctrHead) where

import Frontend.HsTypes

import Utils.Var
import Utils.Annotated
import Utils.FreeVars

import Data.List (nub)

-- | Get the head of a constraint
ctrHead :: Ctr a -> ClsCt a
ctrHead (CtrClsCt  ct)  = ct
ctrHead (CtrImpl _ ctr) = ctrHead ctr
ctrHead (CtrAbs  _ ctr) = ctrHead ctr

-- | The size norm
class SizeOf a where
  sizeOf :: a -> Int

instance SizeOf (MonoTy a) where
  sizeOf (TyCon {})      = 1
  sizeOf (TyApp ty1 ty2) = sizeOf ty1 + sizeOf ty2
  sizeOf (TyVar {})      = 1

instance SizeOf (ClsCt a) where
  sizeOf (ClsCt _ ty) = sizeOf ty

instance SizeOf (Ctr a) where
  sizeOf (CtrClsCt (ClsCt _ ty)) = sizeOf ty
  sizeOf (CtrImpl ctr1 ctr2)     = 1 + sizeOf ctr1 + sizeOf ctr2
  sizeOf (CtrAbs _ ctr)          = sizeOf ctr

-- | Free variable occurrences
class OccOf a t | t -> a where
  occOf :: a -> t -> Int

instance Eq a => OccOf (HsTyVar a) (MonoTy a) where
  occOf _ (TyCon {})      = 0
  occOf a (TyApp ty1 ty2) = occOf a ty1 + occOf a ty2
  occOf a (TyVar b)       = if a == b then 1 else 0

instance Eq a => OccOf (HsTyVar a) (ClsCt a) where
  occOf a (ClsCt _cls ty) = occOf a ty

instance Eq a => OccOf (HsTyVar a) (Ctr a) where
  occOf a (CtrClsCt ct)         = occOf a ct
  occOf a (CtrImpl ctr1 ctr2)   = occOf a ctr1 + occOf a ctr2
  occOf a (CtrAbs (b :| _) ctr)
    | a == b                    = error "OccOf: Shadowing"
    | otherwise                 = occOf a ctr

-- | Termination Condition
termCond :: Eq a => Ctr a -> Bool
termCond (CtrClsCt {}) = True
termCond (CtrAbs _ ct) = termCond ct
termCond (CtrImpl ctr1 ctr2) =  termCond ctr1 && termCond ctr2
                             && sizeOf q1 < sizeOf q2
                             && and [ occOf a q1 <= occOf a q2 | a <- as ]
  where
    q1 = ctrHead ctr1
    q2 = ctrHead ctr2
    as = ftyvsOf (CtrImpl ctr1 ctr2)

-- | Unambiguous constraint
unambigCtr :: Eq a => Ctr a -> Bool
unambigCtr = go []
  where
    go as (CtrClsCt ct)         = as `subsetOf` ftyvsOf ct
    go as (CtrImpl ctr1 ctr2)   = go [] ctr1 && go as ctr2
    go as (CtrAbs (b :| _) ctr)
      | elem b as = error "unambigCtr: Shadowing"
      | otherwise = go (nub (as ++ [b])) ctr --  `subsetOf` ftyvsOf c


