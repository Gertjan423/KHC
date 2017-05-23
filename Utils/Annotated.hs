{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}

-- | All sorts of annotated things.

module Utils.Annotated ( Ann ((:|)), Annotated(..) ) where

import Utils.Unique
import Utils.SnocList
import Utils.PrettyPrint
import Utils.Utils

data Ann a x = a :| x

instance Eq a => Eq (Ann a x) where
  (a1 :| _) == (a2 :| _) = a1 == a2

instance Ord a => Ord (Ann a x) where
  compare (a1 :| _) (a2 :| _) = compare a1 a2

instance Uniquable a => Uniquable (Ann a x) where
    getUnique (a :| _) = getUnique a

instance (PrettyPrint a, PrettyPrint x) => PrettyPrint (Ann a x) where
  ppr (a :| x)  = parens (ppr a <+> colon <+> ppr x)
  needsParens _ = False

instance Functor (Ann a) where
  fmap f (a :| x) = a :| f x

class Annotated a b c | a -> b c where
  (|:) :: b -> c -> a
  labelOf   :: a -> b
  dropLabel :: a -> c

instance Annotated (Ann a x) a x where
  (|:) = (:|)
  labelOf   (a :| _) = a
  dropLabel (_ :| x) = x

instance Annotated [Ann a x] [a] [x] where
  (|:) = zipWithExact (:|)
  labelOf   = map labelOf
  dropLabel = map dropLabel

instance Annotated (SnocList (Ann a x)) (SnocList a) (SnocList x) where
  (|:) as xs = fmap (uncurry (:|)) (zipSnocListExact as xs)
  labelOf    = fmap labelOf
  dropLabel  = fmap dropLabel
