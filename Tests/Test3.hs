
-- * Instance of Show for (GRose f a)
-- ----------------------------------------------------------------------------

-- | Booleans
data Bool = True | False

-- | Lists
data List (a :: *) = LN | LC a (List a)

-- | Generic Rose Trees
data GRose (f :: * -> *) (a :: *)
  = GBranch a (f (GRose f a))

-- | A class to replace the Show class
class () => Bin (a :: *) where {
  bin :: a -> List Bool
}

-- Bin Bool
instance () => Bin Bool where { bin = \x. LC x LN }

instance (Bin a) => Bin (List (a :: *)) where {
  bin = let { concat = \xs. \ys. case xs of
                                   { LN      -> ys
                                   ; LC x xs -> LC x (concat xs ys) } -- shadow xs just for fun
            }
        in \xs. case xs of
                  { LN      -> LN
                  ; LC y ys -> concat (bin y) (bin ys) }
}


-- Bin GRose
instance (Bin a, forall (x :: *). Bin x => Bin (f x)) => Bin (GRose (f :: * -> *) (a :: *)) where {
  bin = let { concat = \xs. \ys. case xs of
                                   { LN      -> ys
                                   ; LC x xs -> LC x (concat xs ys) } -- shadow xs just for fun
            }
        in \tree. case tree of { GBranch x xs -> concat (bin x) (bin xs) }
}

-- | Program expression
bin (GBranch True LN) -- gives rise to wanted constraint: Bin (GRose List Bool)

