{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

-- ----------------------------------------------------------------------------
-- |
-- The technique for generating new Uniques is based on
--
-- 1. The paper ''On Generating Unique Names''
--    by Lennart Augustsson, Mikael Rittri, and Dan Synek and.
--
-- 2. The implementation of Data.Supply by Iavor Diatchki
--    https://hackage.haskell.org/package/value-supply-0.6
--
-- Function naming and classes Uniquable, MonadUnique are similar to the GHC
-- API library UniqSupply
--
-- ----------------------------------------------------------------------------

module Utils.Unique
( -- * The Unique data type
  Unique

  -- * UniqueSupply
, UniqueSupply

  -- * Taking uniques from supplies
, uniqueFromSupply
, uniquesFromSupply
, takeUniqueFromSupply

  -- * Generating new supplies from existing ones
, listSplitUniqueSupply
, splitUniqueSupply
, splitUniqueSupply3
, splitUniqueSupply4

  -- * Creating new supplies
, newUniqueSupply

  -- * The Uniquable class and basic operations
, Uniquable(..), hasKey

  -- * The MonadUnique class
, MonadUnique(..)

  -- * The UniqueSupply monad and basic operations
, UniqueSupplyM(..)
, runUniqueSupplyM
, getUs
, getUniqueUs

  -- * A UniqueSupply monad transformer and instances
, UniqueSupplyT(..), runUniqueSupplyT

  -- * Built in uniques
, arrowTyConUnique, arrowTyVar1Unique, arrowTyVar2Unique
) where

import Utils.PrettyPrint

import Data.Char        ( chr )
import Data.IORef       ( newIORef, atomicModifyIORef )
import System.IO.Unsafe ( unsafeInterleaveIO )

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

-- ----------------------------------------------------------------------------
--                            Arrow TyCon Unique
-- ----------------------------------------------------------------------------

arrowTyConUnique :: Unique
arrowTyConUnique = MkU 'b' 0

arrowTyVar1Unique :: Unique
arrowTyVar1Unique = MkU 'b' 1

arrowTyVar2Unique :: Unique
arrowTyVar2Unique = MkU 'b' 2

-- ----------------------------------------------------------------------------
--                                 Unique
-- ----------------------------------------------------------------------------

-- | The Unique type.
data Unique = MkU {-# UNPACK #-} !Char
                  {-# UNPACK #-} !Int
  deriving (Eq, Ord)

instance PrettyPrint Unique where
  ppr           = text . show
  needsParens _ = False

instance Show Unique where
  show (MkU c i) = c : showIntList i

showIntList :: Int -> String
showIntList i = map chrI ints
  where
    ints | i == 0    = [0]
         | otherwise = intToList i []
    chrI x
      | x < 10    = chr (x+48)
      | otherwise = chr (x+55)
    intToList n ms
      | n == 0               = ms
      | (d,m) <- divMod n 36 = intToList d (m:ms)

incrUnique :: Unique -> Unique
incrUnique (MkU c i) = MkU c (i+1)

-- ----------------------------------------------------------------------------
--                            UniqueSupply
-- ----------------------------------------------------------------------------

-- | The UniqueSupply type (an infinite tree of Uniques)
data UniqueSupply = Node Unique UniqueSupply UniqueSupply

-- | Get the Unique of a UniqueSupply
uniqueFromSupply :: UniqueSupply -> Unique
uniqueFromSupply (Node u _ _) = u

-- | Get an infinite list of Uniques from a UniqueSupply
uniquesFromSupply :: UniqueSupply -> [Unique]
uniquesFromSupply (Node u _ us2) = u : uniquesFromSupply us2

-- | Get the Unique of a UniqueSupply
takeUniqueFromSupply :: UniqueSupply -> (Unique, UniqueSupply)
takeUniqueFromSupply (Node u us1 _) = (u, us1)

-- | Generate an infinite list of supplies
listSplitUniqueSupply :: UniqueSupply -> [UniqueSupply]
listSplitUniqueSupply (Node _ us1 us2) = us1 : listSplitUniqueSupply us2

-- | Generate two new supplies from one (both are different from the given)
splitUniqueSupply :: UniqueSupply -> (UniqueSupply, UniqueSupply)
splitUniqueSupply (Node _ us1 us2) = (us1, us2)

-- | Generate three new supplies from one (both are different from the given)
splitUniqueSupply3 :: UniqueSupply -> (UniqueSupply, UniqueSupply, UniqueSupply)
splitUniqueSupply3 (Node _ us1 (Node _ us2 us3)) = (us1, us2, us3)

-- | Generate four new supplies from one (both are different from the given)
splitUniqueSupply4 :: UniqueSupply -> (UniqueSupply, UniqueSupply, UniqueSupply, UniqueSupply)
splitUniqueSupply4 (Node _ us1 (Node _ us2 (Node _ us3 us4))) = (us1, us2, us3, us4)

-- | Create a new UniqueSupply out of thin air. The character given must be
-- distinct from all previous calls to this function for the Uniques generated
-- to be truly unique.
newUniqueSupply :: Char -> IO UniqueSupply
newUniqueSupply c = gen =<< newIORef (MkU c 0)
  where gen r = unsafeInterleaveIO
              $ do v  <- unsafeInterleaveIO (atomicModifyIORef r upd)
                   ls <- gen r
                   rs <- gen r
                   return (Node v ls rs)
        upd a = let b = incrUnique a in seq b (b, a)
{-# INLINE newUniqueSupply #-}
-- HINT: Always call with a lowercase letter, it looks nicer :-)

-- ----------------------------------------------------------------------------
--                               Uniquable
-- ----------------------------------------------------------------------------

-- | A class for all things we can obtain a Unique from
class Uniquable a where
  getUnique :: a -> Unique

-- | Check whether a Uniquable object has a specific key
hasKey :: Uniquable a => a -> Unique -> Bool
hasKey x k = getUnique x == k

-- ----------------------------------------------------------------------------
--                              MonadUnique
-- ----------------------------------------------------------------------------

-- | A monad for generating unique identifiers
class Monad m => MonadUnique m where
  -- | Get a new UniqueSupply
  getUniqueSupplyM :: m UniqueSupply
  -- | Get a new unique identifier
  getUniqueM       :: m Unique
  -- | Get an infinite list of new unique identifiers
  getUniquesM      :: m [Unique]

  -- And some default implementations..
  getUniqueM  = uniqueFromSupply  <$> getUniqueSupplyM
  getUniquesM = uniquesFromSupply <$> getUniqueSupplyM

-- ----------------------------------------------------------------------------
--                             UniqueSupplyM
-- ----------------------------------------------------------------------------

-- | A monad for generating Uniques
newtype UniqueSupplyM a = USM { unUSM :: UniqueSupply -> (a, UniqueSupply) }

-- | Run a UniqueSupplyM computation
runUniqueSupplyM :: UniqueSupplyM a -> UniqueSupply -> (a, UniqueSupply)
runUniqueSupplyM (USM m) us = case m us of
  (u, us') -> (u, us')

-- | Get a UniqueSupply within the UniqueSupplyM monad
getUs :: UniqueSupplyM UniqueSupply
getUs = USM (\us -> case splitUniqueSupply us of
                      (us1, us2) -> (us1, us2))

-- | Get a Unique within the UniqueSupplyM monad
getUniqueUs :: UniqueSupplyM Unique
getUniqueUs = USM (\us -> case takeUniqueFromSupply us of
  (u, us') -> (u, us'))

-- GEORGE: Make UniqueSupplyM use a strict tuple instead?
-- It would need unboxed tuples

-------------------------------------------------------------------------------

instance Functor UniqueSupplyM where
  fmap f (USM m) = USM (\us -> case m us of (r, us1) -> (f r, us1))
  {-# INLINE fmap #-}

instance Applicative UniqueSupplyM where
  pure x = USM (\us -> (x, us))
  {-# INLINE pure #-}
  (USM f) <*> (USM m) = USM (\us -> case f us of
                     (ff, us1) -> case m us1 of
                       (xx, us2) -> (ff xx, us2))
  {-# INLINE (<*>) #-}

instance Monad UniqueSupplyM where
  return x = USM (\us -> (x, us))
  {-# INLINE return #-}
  USM m >>= f = USM (\us -> case m us of
                              (x, us1) -> unUSM (f x) us1)
  {-# INLINE (>>=) #-}

instance MonadUnique UniqueSupplyM where
  getUniqueSupplyM = getUs
  {-# INLINE getUniqueSupplyM #-}

-- ----------------------------------------------------------------------------
--                             UniqueSupplyT
-- ----------------------------------------------------------------------------

-- | The UniqueSupply monad transformer
newtype UniqueSupplyT m a = UST { unUST :: UniqueSupply -> m (a, UniqueSupply) }

runUniqueSupplyT :: UniqueSupplyT m a -> UniqueSupply -> m (a, UniqueSupply)
runUniqueSupplyT = unUST

instance Functor m => Functor (UniqueSupplyT m) where
  fmap f (UST m) = UST (\us -> fmap (\(x,y) -> (f x, y)) (m us))
  {-# INLINE fmap #-}

instance Monad m => Applicative (UniqueSupplyT m) where
  pure x = UST (\us -> return (x,us))
  {-# INLINE pure #-}
  UST mf <*> UST mx = UST (\us0 -> do
    (f, us1) <- mf us0
    (x, us2) <- mx us1
    return (f x, us2))
  {-# INLINE (<*>) #-}

instance Monad m => Monad (UniqueSupplyT m) where
  return x = UST (\us -> return (x,us))
  {-# INLINE return #-}
  UST m >>= f = UST (\us0 -> m us0 >>= \(x,us1) -> unUST (f x) us1)
  {-# INLINE (>>=) #-}
  fail str = UST (\_ -> fail str)
  {-# INLINE fail #-}

instance Monad m => MonadUnique (UniqueSupplyT m) where
  getUniqueSupplyM = UST (\us -> case splitUniqueSupply us of
    (us1, us2) -> return (us1, us2))

instance MonadTrans UniqueSupplyT where
  lift m = UST $ \us -> m >>= \x -> return (x, us)
  -- lift :: Monad m => m a -> t m a

mapUniqueSupplyT :: (m (a, UniqueSupply) -> n (b, UniqueSupply)) -> UniqueSupplyT m a -> UniqueSupplyT n b
mapUniqueSupplyT f m = UST (f . unUST m)

instance MonadState s m => MonadState s (UniqueSupplyT m) where
  get   = lift get      -- get :: m s
  put   = lift . put    -- put :: s -> m ()
  state = lift . state  -- state :: (s -> (a, s)) -> m a

instance MonadReader r m => MonadReader r (UniqueSupplyT m) where
  ask    = lift ask                 -- ask :: m r
  local  = mapUniqueSupplyT . local -- local :: (r -> r) -> m a -> m a
  reader = lift . reader            -- reader :: (r -> a) -> m a

instance MonadError e m => MonadError e (UniqueSupplyT m) where
  throwError = lift . throwError  -- throwError :: e -> m a
  catchError m h = UST $ \us ->   -- catchError :: m a -> (e -> m a) -> m a
    catchError (unUST m us) (\e -> unUST (h e) us)

instance MonadWriter w m => MonadWriter w (UniqueSupplyT m) where
  writer   = lift . writer    -- writer :: (a, w) -> m a
  tell     = lift . tell      -- tell :: w -> m ()
  listen m = UST $ \us -> do  -- listen :: m a -> m (a, w)
    ((a, us'), w) <- listen (unUST m us)
    return ((a, w), us')
  pass action   = UST $ \us -> pass $ do -- pass :: m (a, w -> w) -> m a
    ((a, f), us') <- unUST action us
    return ((a, us'), f)

instance MonadIO m => MonadIO (UniqueSupplyT m) where
  liftIO = lift . liftIO   -- liftIO :: IO a -> m a
