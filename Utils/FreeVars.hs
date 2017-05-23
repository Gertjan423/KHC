{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}

-- | Class ContainsFreeTyVars: collect variables from objects

module Utils.FreeVars (ContainsFreeTyVars(..), subsetOf) where

import Data.List (nub, (\\))

-- | Collect the free variables from objects
class ContainsFreeTyVars t tv | t -> tv where
  ftyvsOf :: t -> [tv]

instance (Eq tv, ContainsFreeTyVars a tv) => ContainsFreeTyVars [a] tv where
  ftyvsOf = nub . concatMap ftyvsOf

instance (Eq tv, ContainsFreeTyVars a tv, ContainsFreeTyVars b tv) => ContainsFreeTyVars (a, b) tv where
  ftyvsOf (x,y) = nub (ftyvsOf x ++ ftyvsOf y)

-- | Check whether the first list is a subset of the second (trated as sets)
subsetOf :: Eq a => [a] -> [a] -> Bool
subsetOf xs ys = (xs \\ ys) == []

