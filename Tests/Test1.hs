
-- * MonadTrans Example
-- ----------------------------------------------------------------------------

-- | Transformer composition:
--     newtype (t1 * t2) m a = C { runC :: t1 (t2 m) a }
data Comp (t1 :: (* -> *) -> * -> *)
          (t2 :: (* -> *) -> * -> *)
          (m  :: * -> *) (a :: *)
  = C (t1 (t2 m) a)

-- | Simplified Monad class
class () => Monad (m :: * -> *) where {
  bind :: forall (a :: *). forall (b :: *). m a -> (a -> m b) -> m b
}

-- | The MonadTrans class with Quantified Class Constraints
class (forall (m :: * -> *). Monad m => Monad (t m))
    => Trans (t :: (* -> *) -> (* -> *)) where {
  lift :: forall (m :: * -> *). forall (a :: *). Monad m => m a -> t m a
}

-- | Trans instance for transformer composition
instance (Trans t1, Trans t2) => Trans (Comp (t1 :: (* -> *) -> (* -> *)) (t2 :: (* -> *) -> (* -> *))) where {
  lift = \x. C (lift (lift x))
}

-- | Program expression
\x. x

