{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.FreeVars (ContainsFreeTyVars(..), subsetOf, ContainsFreeTmVars(..)) where

import Data.List (nub, (\\))

--
-- TODO: merge ContainsFreeTyVars and ContainsFreeTmVars
--

-- | Class ContainsFreeTyVars: collect type variables from objects

-- | Collect the free variables from objects
class ContainsFreeTyVars t tv | t -> tv where
  ftyvsOf :: t -> [tv]

instance (Eq tv, ContainsFreeTyVars a tv) => ContainsFreeTyVars [a] tv where
  ftyvsOf = nub . concatMap ftyvsOf

instance (Eq tv, ContainsFreeTyVars a tv, ContainsFreeTyVars b tv) => ContainsFreeTyVars (a, b) tv where
  ftyvsOf (x,y) = nub (ftyvsOf x ++ ftyvsOf y)

-- | Check whether the first list is a subset of the second (treated as sets)
subsetOf :: Eq a => [a] -> [a] -> Bool
subsetOf xs ys = null (xs \\ ys)

-- | Class ContainsFreeTmVars: collect term variables from terms
class ContainsFreeTmVars tm v | tm -> v where
  ftmvsOf :: tm -> [v]

instance (Eq v, ContainsFreeTmVars tm v) => ContainsFreeTmVars [tm] v where
  ftmvsOf = nub . concatMap ftmvsOf

instance (Eq v, ContainsFreeTmVars tm1 v, ContainsFreeTmVars tm2 v) => ContainsFreeTmVars (tm1, tm2) v where
  ftmvsOf (x,y) = nub (ftmvsOf x ++ ftmvsOf y)