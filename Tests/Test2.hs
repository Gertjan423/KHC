
-- * Example program illustrating KHC bug
-- *   What are the type instantiations for type variable "b"
-- *   of method "method", used in the instance declaration for class "Pure"?
-- *   No constraints exist for "b", so any type is allowed.
-- *   The KHC bug is that KHC did not bind or substitute "b"
-- *   for any specific type, leaving free variables in the resulting terms.
-- ----------------------------------------------------------------------------

data List (a :: *) = Cons a (List a) | Nil

data Pair (a :: *) (b :: *) = Pair a b

class Fst p :: * -> * -> * where
  fst :: forall (a :: *) . forall (b :: *) . p a b -> a
class Snd p :: * -> * -> * where
  snd :: forall (a :: *) . forall (b :: *) . p a b -> b
instance Fst Pair where
  fst = \p. case p of
              Pair x y -> x
instance Snd Pair where
  snd = \p. case p of
              Pair x y -> y

data Maybe (a :: *) = Just a | Nothing

class Applicative f :: * -> * where
  method :: forall (a :: *) .
            forall (b :: *) .
			Pair (a -> f a) (f (a -> b) -> f a -> f b)

class Pure f :: * -> * where
  pure :: forall (a :: *) . a -> f a
class Apply f :: * -> * where
  apply :: forall (a :: *) .
           forall (b :: *) .
		   f (a -> b) -> f a -> f b
instance Applicative f => Pure (f :: * -> *) where
  pure = fst method
instance Applicative f => Apply (f :: * -> *) where
  apply = snd method

instance Applicative Maybe where
  method = Pair Just
                (\m.\n. case m of
                          Just f  -> case n of
                                       Just x  -> Just (f x)
                                       Nothing -> Nothing
                          Nothing -> Nothing)

-- | Program expression
(method)
