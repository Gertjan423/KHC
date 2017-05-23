{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

-- The following code is a replica of the module Control.Monad.Logic:

-------------------------------------------------------------------------
-- |
-- Module      : Control.Monad.Logic
-- Copyright   : (c) Dan Doel
-- License     : BSD3
--
-- Maintainer  : dan.doel@gmail.com
-- Stability   : experimental
-- Portability : non-portable (multi-parameter type classes)
--
-- A backtracking, logic programming monad.
--
--    Adapted from the paper
--    /Backtracking, Interleaving, and Terminating
--        Monad Transformers/, by
--    Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry
--    (<http://www.cs.rutgers.edu/~ccshan/logicprog/ListT-icfp2005.pdf>).
-------------------------------------------------------------------------

module Utils.ListT where

import Utils.SnocList
import Utils.Errors
import Utils.PrettyPrint

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
-- import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Data.List

-- | A monad transformer for performing backtracking computations
newtype ListT m a =
    ListT { unListT :: forall r. (a -> m r -> m r) -> m r -> m r }

-- | Get the list of the successful ones (the list is "reversed", since we do
-- the search right-to-left, like a proper lookup should)
snocListChooseM :: Monad m => SnocList a -> (a -> m (Maybe b)) -> m [b]
snocListChooseM SN        _f = return []
snocListChooseM (xs :> x)  f = f x >>= \case
  Nothing -> snocListChooseM xs f
  Just y  -> fmap (y:) (snocListChooseM xs f)

-- | Non-deterministically select one of the elements of a list
selectListT :: Monad m => [a] -> ListT m a
selectListT xs = foldr (<|>) mzero (map pure xs)

firstMatch :: (MonadError String m, Monad m) => ListT m a -> m a
firstMatch list = runListT list goM (pure Nothing) >>= \case
  Nothing -> throwErrorM (text "Solving failed") -- GEORGE: This information is kinda useless.
                                                 -- Find a way to show the residuals
  Just x  -> return x
  where
    goM res mres = mres >>= return . Just . \case
      Just res' -> res'
      Nothing   -> res

-------------------------------------------------------------------------
-- | Extract the first result from a ListT computation

firstListT :: Monad m => ListT m a -> m a
firstListT lt = unListT lt (const . return) (fail "firstListT: No answer")

-- -------------------------------------------------------------------------
-- | Extract the first result from a ListT computation that satisfies a predicate

firstSuchThatListT :: Monad m => (a -> Bool) -> ListT m a -> m a
firstSuchThatListT p m = do
  xs <- filter p <$> unListT m (liftM . (:)) (return [])
  case uncons xs of
    Nothing    -> fail "firstSuchThatListT: No answer"
    Just (x,_) -> return x

-------------------------------------------------------------------------
-- | Runs a ListT computation with the specified initial success and
-- failure continuations.
runListT :: ListT m a -> (a -> m r -> m r) -> m r -> m r
runListT = unListT

instance Functor (ListT f) where
    fmap f lt = ListT $ \sk fk -> unListT lt (sk . f) fk

instance Applicative (ListT f) where
    pure a = ListT $ \sk fk -> sk a fk
    f <*> a = ListT $ \sk fk -> unListT f (\g fk' -> unListT a (sk . g) fk') fk

instance Alternative (ListT f) where
    empty = ListT $ \_ fk -> fk
    f1 <|> f2 = ListT $ \sk fk -> unListT f1 sk (unListT f2 sk fk)

instance Monad (ListT m) where
    m >>= f = ListT $ \sk fk -> unListT m (\a fk' -> unListT (f a) sk fk') fk
    fail _ = ListT $ \_ fk -> fk

instance MonadPlus (ListT m) where
    mzero = ListT $ \_ fk -> fk
    m1 `mplus` m2 = ListT $ \sk fk -> unListT m1 sk (unListT m2 sk fk)

instance MonadTrans ListT where
  lift m = ListT $ \sk fk -> m >>= \a -> sk a fk

instance (MonadIO m) => MonadIO (ListT m) where
    liftIO = lift . liftIO

-- Needs undecidable instances
instance MonadReader r m => MonadReader r (ListT m) where
    ask = lift ask
    local f m = ListT $ \sk fk -> unListT m ((local f .) . sk) (local f fk)

-- Needs undecidable instances
instance MonadState s m => MonadState s (ListT m) where
    get = lift get
    put = lift . put

-- Needs undecidable instances
instance MonadError e m => MonadError e (ListT m) where
  throwError = lift . throwError
  catchError m h = ListT $ \sk fk -> let
      handle r = r `catchError` \e -> unListT (h e) sk fk
    in handle $ unListT m (\a -> sk a . handle) fk

