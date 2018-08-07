{-# LANGUAGE FunctionalDependencies #-}

module Frontend.Conditions (unambigCtr, termCond, ctrHead) where

import Frontend.HsTypes

import Utils.Var
import Utils.Annotated
import Utils.FreeVars

-- | Get the head of a constraint
ctrHead :: Ctr a -> ClsCt a
ctrHead (Ctr _ _ ct) = ct

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
  sizeOf (Ctr _ cs ct) = sizeOf ct + foldl (flip $ \c -> (+) (sizeOf c)) 1 cs

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
  occOf a (Ctr as cs ct)
    | elem a (map labelOf as) = error "OccOfL Shadowing"
    | otherwise = occOf a ct + foldl (+) 1 (map (occOf a) cs)

-- | Termination Condition
termCond :: Eq a => Ctr a -> Bool
termCond (Ctr as cs ct) =  and [ sizeOf c < sizeOf ct | c <- cs ]
                       && and [ occOf b c <= occOf b ct | c <- cs , b <- bs ]
  where
    bs = ftyvsOf (Ctr as cs ct)

-- | Unambiguous constraint
unambigCtr :: Eq a => Ctr a -> Bool
unambigCtr (Ctr as _ ct) = (map labelOf as) `subsetOf` ftyvsOf ct


