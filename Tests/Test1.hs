
-- * Simple example with superclasses
-- ----------------------------------------------------------------------------

data Bool = True | False

class Eq a :: * where
  equals :: a -> a -> Bool

class Eq a => Ord a :: * where
  compare :: a -> a -> Bool

instance Eq Bool where
  equals = \x. \y. case x of
      True -> case y of
          True -> True
          False -> False
      False -> case y of
          True -> False
          False -> True

-- | Program expression
\x. x

