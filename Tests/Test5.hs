
-- * Instance of Show for (HPerfect h a)
-- ----------------------------------------------------------------------------

-- | Booleans
data Bool = True | False

-- | Lists
data List (a :: *) = LN | LC a (List a)

-- | Tuples
data Tup (a :: *) (b :: *) = MkTup a b

-- | Perfect Trees
data HPerfect (f :: * -> *) (a :: *)
  = HZero a
  | HSucc (f (Tup a a))

-- | Fixpoint:
--     data Mu h a = In (h (Mu h) a)
data Mu (h :: (* -> *) -> * -> *) (a :: *)
  = In (h (Mu h) a)

-- | A class to replace the Show class
class () => Bin (a :: *) where {
  bin :: a -> List Bool
}

-- Bin Tup
instance (Bin a, Bin b) => Bin (Tup (a :: *) (b :: *)) where {
  bin = let { concat = \xs. \ys. case xs of
                                   { LN      -> ys
                                   ; LC x xs -> LC x (concat xs ys) } -- shadow xs just for fun
            }
        in  \tup. case tup of { MkTup x y -> concat (bin x) (bin y) }
}

-- Bin Bool
instance () => Bin Bool where { bin = \x. LC x LN }

-- Bin Mu
instance ( Bin a
         , forall (f :: * -> *). forall (c :: *). Bin c => (forall (b :: *). Bin b => Bin (f b)) => Bin (h f c)
         ) => Bin (Mu (h :: (* -> *) -> (* -> *)) (a :: *)) where { bin = \x. case x of { In y -> bin y } }

-- Bin HPerfect
instance (Bin a, forall (c :: *). Bin c => Bin (f c)) => Bin (HPerfect (f :: * -> *) (a :: *)) where {
  bin = \tm. case tm of
             { HZero x  -> bin x
             ; HSucc xs -> bin xs }
}

-- | Program expression
bin (In (HZero True))

