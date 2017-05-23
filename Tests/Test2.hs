
-- * Functor Instance For (Mu h) Example
-- ----------------------------------------------------------------------------

-- | Fixpoint:
--     data Mu h a = In (h (Mu h) a)
data Mu (h :: (* -> *) -> * -> *) (a :: *)
  = In (h (Mu h) a)

-- | The Functor class
class () => Functor (f :: * -> *) where {
  fmap :: forall (a :: *). forall (b :: *). (a -> b) -> f a -> f b
}

-- | Functor instance for Mu
instance (forall (f :: * -> *). Functor f => Functor (h f)) => Functor (Mu (h :: (* -> *) -> (* -> *))) where {
  fmap = \f. \y. case y of { In x -> In (fmap f x) }

}

-- | Program expression
\x. x

