
module Utils.AssocList
( AssocList(..), lookupInAssocList, extendAssocList, adjustAssocList
, mapFstWithDataAssocList, mapAssocListM, mapAssocListM_ -- make it completely opaque
) where

import Utils.SnocList
import Utils.PrettyPrint
import Control.Arrow (second)

-- * Association Lists
-- ------------------------------------------------------------------------------

newtype AssocList a b = AssocList (SnocList (a,b))

instance Monoid (AssocList a b) where
  mempty = AssocList mempty
  mappend (AssocList xs) (AssocList ys) = AssocList (mappend xs ys)
  mconcat = foldl mappend mempty -- foldl since mappend does induction on the second argument

instance Functor (AssocList a) where
  fmap f (AssocList xs) = AssocList (fmap (second f) xs)

-- GEORGE: Hate the name. Find something appropriate if possible.
mapFstWithDataAssocList :: (a -> b -> c) -> AssocList a b -> AssocList c b
mapFstWithDataAssocList f (AssocList ys) = AssocList (go ys)
  where
    go SN            = SN
    go (xs :> (x,y)) = go xs :> (f x y, y)

mapAssocListM :: Monad m => ((a, b) -> m (c, d)) -> AssocList a b -> m (AssocList c d)
mapAssocListM f (AssocList list) = go list >>= return . AssocList
  where
    go SN        = return SN
    go (xs :> x) = (:>) <$> go xs <*> f x

mapAssocListM_ :: Monad m => ((a, b) -> m c) -> AssocList a b -> m ()
mapAssocListM_ f (AssocList list) = go list
  where
    go SN        = return ()
    go (xs :> x) = go xs <* f x

lookupInAssocList :: Eq a => a -> AssocList a b -> Maybe b
lookupInAssocList x (AssocList xs) = lookupSLMaybe f xs
  where f (y,val) = if x == y then Just val else Nothing

-- GEORGE: I would have preferred to pass them to the right but this means
-- (ugly) changes all over the place. Leaving this as a TODO.
extendAssocList :: a -> b -> AssocList a b -> AssocList a b
extendAssocList a b (AssocList xs) = AssocList (xs :> (a,b))

-- | Adjust ALL entries with this key
adjustAssocList :: Eq a => a -> (b -> b) -> AssocList a b -> AssocList a b
adjustAssocList x f (AssocList xs) = AssocList (go xs)
  where
    go SN                        = SN
    go (ys :> (y,v)) | x == y    = go ys :> (y, f v) -- apply the function
                     | otherwise = go ys :> (y, v)   -- leave untouched

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (AssocList a b) where
  ppr (AssocList xs) = ppr xs
  needsParens _      = False
