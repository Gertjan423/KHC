
-- * Instance of Show for (Mu h a)
-- ----------------------------------------------------------------------------

-- | Booleans
data Bool = True | False

-- | Lists
data List (a :: *) = LN | LC a (List a)

-- | Fixpoint:
--     data Mu h a = In (h (Mu h) a)
data Mu (h :: (* -> *) -> * -> *) (a :: *)
  = In (h (Mu h) a)

-- | A class to replace the Show class
class () => Bin (a :: *) where {
  bin :: a -> List Bool
}

-- Bin Mu
instance ( Bin a
         , forall (f :: * -> *). forall (c :: *). Bin c => (forall (b :: *). Bin b => Bin (f b)) => Bin (h f c)
         ) => Bin (Mu (h :: (* -> *) -> (* -> *)) (a :: *)) where { bin = \x. case x of { In y -> bin y } }

-- | Program expression
\x. x

