{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}

module Utils.SnocList
( SnocList(..), snocListToList, listToSnocList, snocListLength
, lookupSLMaybe      -- rename to lookupSL
, monoidFoldSnocList -- I don't like this one
, lookupSLMaybeM
, lookupSLMaybeMatchM, mapSnocListM, forSnocListM, zipWithSnocListM, singletonSnocList
, foldZipWithSnocList, unzipSnocList, unzipWithSnocList, zipSnocListExact, zipWithSnocList
, findSLMaybeM
) where

import Data.List (nub)
import Utils.PrettyPrint
import Utils.FreeVars

-- | SnocLists
data SnocList a = SN | (SnocList a) :> a
  deriving (Eq)

-- | Transform a SnocList to a common list
snocListToList :: SnocList a -> [a]
snocListToList = reverse . go
  where
    go :: SnocList a -> [a]
    go SN        = []
    go (xs :> x) = x : go xs

listToSnocList :: [a] -> SnocList a
listToSnocList = go . reverse
  where
    go :: [a] -> SnocList a
    go []     = SN
    go (x:xs) = go xs :> x

instance PrettyPrint a => PrettyPrint (SnocList a) where
  ppr           = ppr . snocListToList
  needsParens _ = False

instance Semigroup (SnocList a) where
  (<>) xs SN        = xs
  (<>) xs (ys :> y) = (<>) xs ys :> y

instance Monoid (SnocList a) where
  mempty = SN
  mconcat = foldl mappend SN -- foldl since mappend does induction on the second argument

instance Functor SnocList where
  fmap _f SN        = SN
  fmap  f (xs :> x) = fmap f xs :> f x

instance (Eq tv, ContainsFreeTyVars a tv) => ContainsFreeTyVars (SnocList a) tv where
  ftyvsOf = nub . concatMap ftyvsOf . snocListToList

-- | mapM for SnocList
mapSnocListM :: Monad m => (a -> m b) -> SnocList a -> m (SnocList b)
mapSnocListM _f SN        = return SN
mapSnocListM  f (xs :> x) = do
  ys <- mapSnocListM f xs
  y  <- f x
  return (ys :> y)

-- | forM for SnocList
forSnocListM :: Monad m => SnocList a -> (a -> m b) -> m (SnocList b)
forSnocListM list f = mapSnocListM f list
{-# INLINE forSnocListM #-}

zipWithSnocListM :: Monad m => (a -> b -> m c) -> SnocList a -> SnocList b -> m (SnocList c)
zipWithSnocListM _f SN        SN        = return SN
zipWithSnocListM  f (xs :> x) (ys :> y) = do
  zs <- zipWithSnocListM f xs ys
  z  <- f x y
  return (zs :> z)
zipWithSnocListM _f _xs _ys = error "zipWithSnocListM: length mismatch"

-- | GEORGE Says: I don't like this.
monoidFoldSnocList :: Monoid a => SnocList a -> a
monoidFoldSnocList SN        = mempty
monoidFoldSnocList (xs :> x) = monoidFoldSnocList xs `mappend` x

-- | Create a singleton SnocList
singletonSnocList :: a -> SnocList a
singletonSnocList x = SN :> x

-- | Compute the length of a SnocList
snocListLength :: SnocList a -> Int
snocListLength SN        = 0
snocListLength (xs :> _) = snocListLength xs + 1


foldZipWithSnocList :: Monoid m => (a -> b -> m) -> SnocList a -> SnocList b -> m
foldZipWithSnocList _f SN        SN        = mempty
foldZipWithSnocList  f (xs :> x) (ys :> y) = foldZipWithSnocList f xs ys `mappend` f x y
foldZipWithSnocList _f _xs       _ys       = error "foldZipWithSnocList: length mismatch"

-- | Lookup something in a SnocList based on a Maybe-predicate
lookupSLMaybe :: (a -> Maybe b) -> SnocList a -> Maybe b
lookupSLMaybe _p SN        = Nothing
lookupSLMaybe  p (xs :> x) = case p x of
  Just y  -> Just y
  Nothing -> lookupSLMaybe p xs

-- | Lookup something in a SnocList based on a monadic Maybe-predicate
lookupSLMaybeM :: Monad m => (a -> m (Maybe b)) -> SnocList a -> m (Maybe b)
lookupSLMaybeM _p SN        = return Nothing
lookupSLMaybeM  p (xs :> x) = p x >>= \case
  Just y  -> return (Just y)
  Nothing -> lookupSLMaybeM p xs

-- | Lookup something in a SnocList based on a monadic Maybe-predicate
-- Return the matching SnocList element as well
lookupSLMaybeMatchM :: Monad m => (a -> m (Maybe b)) -> SnocList a -> m (Maybe (a, b))
lookupSLMaybeMatchM _p SN        = return Nothing
lookupSLMaybeMatchM  p (xs :> x) = p x >>= \case
  Just y  -> return (Just (x, y))
  Nothing -> lookupSLMaybeMatchM p xs

findSLMaybeM :: Monad m => (a -> m (Maybe b)) -> SnocList a -> m (Maybe (SnocList a, b))
findSLMaybeM _f SN = return Nothing
findSLMaybeM  f (xs :> x) = f x >>= \case
  Just y  -> return (Just (xs, y))
  Nothing -> findSLMaybeM f xs >>= \case
    Just (ys, y) -> return (Just (ys :> x, y))
    Nothing      -> return Nothing

-- | Unzip a SnocList of tuples to two lists
unzipSnocList :: SnocList (a, b) -> (SnocList a, SnocList b)
unzipSnocList SN            = (SN, SN)
unzipSnocList (xs :> (y,z)) = (ys :> y, zs :> z) where (ys, zs) = unzipSnocList xs

-- | Unzip a SnocList to two lists using a function
unzipWithSnocList :: (a -> (b, c)) -> SnocList a -> (SnocList b, SnocList c)
unzipWithSnocList _f SN        = (SN, SN)
unzipWithSnocList  f (xs :> x) = (ys :> y, zs :> z)
  where
    (ys, zs) = unzipWithSnocList f xs
    (y, z)   = f x

-- | Zips two SnocLists into a SnocList of tuples
-- If the two SnocLists are not equally long, the remainder is thrown away
zipSnocList :: SnocList a -> SnocList b -> SnocList (a, b)
zipSnocList SN        _         = SN
zipSnocList _         SN        = SN
zipSnocList (as :> a) (bs :> b) = (zipSnocList as bs) :> (a, b)

-- | Zip two SnocLists into a SnocList of tuples. Fail if lengths don't match.
zipSnocListExact :: SnocList a -> SnocList b -> SnocList (a, b)
zipSnocListExact (as :> a) (bs :> b) = (zipSnocList as bs) :> (a, b)
zipSnocListExact SN        SN        = SN
zipSnocListExact _         _         = error "zipSnocListExact: length mismatch"

zipWithSnocList :: (a -> b -> c) -> SnocList a -> SnocList b -> SnocList c
zipWithSnocList _f SN        SN        = SN
zipWithSnocList  f (xs :> x) (ys :> y) = zipWithSnocList f xs ys :> f x y
zipWithSnocList _f _xs       _ys       = error "zipWithSnocList: length mismatch"
