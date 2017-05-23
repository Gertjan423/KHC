
-- * Some Datatype Declarations
-- ----------------------------------------------------------------------------

-- | The Unit type
data Unit = MkUnit

-- | Booleans
data Bool = True | False

-- | Lists
data List (a :: *) = LN | LC a (List a)

-- | Natural numbers
data Nat = Zero | Succ Nat

-- | The Identity Functor
data Id (a :: *) = MkId a

-- | Generic Rose Trees
data GRose (f :: * -> *) (a :: *)
  = GBranch a (f (GRose f a))

-- | Transformer composition:
--     newtype (t1 * t2) m a = C { runC :: t1 (t2 m) a }
data Comp (t1 :: (* -> *) -> * -> *)
          (t2 :: (* -> *) -> * -> *)
          (m  :: * -> *) (a :: *)
  = C (t1 (t2 m) a)

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

-- * Some Class Declarations
-- ----------------------------------------------------------------------------

-- | A class to replace the Show class
class () => Bin (a :: *) where {
  bin :: a -> List Bool
}

-- | Simplified Eq class
class () => Eq (a :: *) where {
  eq :: a -> a -> Bool
}

-- | Simplified Ord class
class (Eq a) => Ord (a :: *) where {
  le :: a -> a -> Bool
}

-- | Simplified Monad class
class () => Monad (m :: * -> *) where {
  bind :: forall (a :: *). forall (b :: *). m a -> (a -> m b) -> m b
}

-- | The MonadTrans class with Quantified Class Constraints
class (forall (m :: * -> *). Monad m => Monad (t m))
    => Trans (t :: (* -> *) -> (* -> *)) where {
  lift :: forall (m :: * -> *). forall (a :: *). Monad m => m a -> t m a
}

-- | The Functor class
class () => Functor (f :: * -> *) where {
  fmap :: forall (a :: *). forall (b :: *). (a -> b) -> f a -> f b
}

-- * Some Class Instances
-- ----------------------------------------------------------------------------

-- Eq Unit
instance () => Eq Unit where {
  eq = \x. \y. True
}

-- Ord Unit
instance () => Ord Unit where {
  le = \x. \y. True
}

-- Eq Id
instance (Eq a) => Eq (Id (a :: *)) where {
  eq = \x. \y. case x of {
                 MkId x -> case y of { MkId y -> eq x y }
               }
}

-- Bin GRose
instance (Bin a, forall (x :: *). Bin x => Bin (f x)) => Bin (GRose (f :: * -> *) (a :: *)) where {
  bin = let { concat = \xs. \ys. case xs of
                                   { LN      -> ys
                                   ; LC x xs -> LC x (concat xs ys) } -- shadow xs just for fun
            }
        in \tree. case tree of { GBranch x xs -> concat (bin x) (bin xs) }
}

-- Bin Tup
instance (Bin a, Bin b) => Bin (Tup (a :: *) (b :: *)) where {
  bin = let { concat = \xs. \ys. case xs of
                                   { LN      -> ys
                                   ; LC x xs -> LC x (concat xs ys) } -- shadow xs just for fun
            }
        in  \tup. case tup of { MkTup x y -> concat (bin x) (bin y) }
}

-- Bin HPerfect
instance (Bin a, forall (c :: *). Bin c => Bin (f c)) => Bin (HPerfect (f :: * -> *) (a :: *)) where {
  bin = \tm. case tm of
             { HZero x  -> bin x
             ; HSucc xs -> bin xs }
}

-- Bin Mu
instance ( Bin a
         , forall (f :: * -> *). forall (c :: *). Bin c => (forall (b :: *). Bin b => Bin (f b)) => Bin (h f c)
         ) => Bin (Mu (h :: (* -> *) -> (* -> *)) (a :: *)) where { bin = \x. case x of { In y -> bin y } }


-- Trans Comp
instance (Trans t1, Trans t2) => Trans (Comp (t1 :: (* -> *) -> (* -> *)) (t2 :: (* -> *) -> (* -> *))) where {
  lift = \x. C (lift (lift x))
}

-- Functor Mu
instance (forall (f :: * -> *). Functor f => Functor (h f)) => Functor (Mu (h :: (* -> *) -> (* -> *))) where {
  fmap = \f. \y. case y of { In x -> In (fmap f x) }

}

-- * Final Program Expression
-- ----------------------------------------------------------------------------

\x. x

-- || -- * The termination example from the paper
-- || -- ------------------------------------------------------------------------------
-- ||
-- || paper_tests :: PsProgram
-- || paper_tests = list_decl
-- ||             $ bool_decl
-- ||             $ bin_decl -- Replacement for Show
-- ||             $ nat_decl
-- ||             $ unit_decl
-- ||             $ eq_decl
-- ||             $ eq_unit_inst
-- ||
-- ||               -- Example 1.
-- ||               --   instance (...) => Trans (Comb t1 t2)
-- ||             $ monad_decl
-- ||             $ trans_decl
-- ||             $ comb_decl
-- ||             $ trans_comb_inst
-- ||
-- ||               -- Example 2.
-- ||               --   instance (...) => Functor (Mu h)
-- ||             $ functor_decl
-- ||             $ mu_decl
-- ||             $ functor_mu_inst
-- ||
-- ||               -- Example 3.
-- ||               --   instance (...) => Bin (GRose f a)
-- ||             $ grose_decl
-- ||             $ bin_grose_inst
-- ||
-- ||               -- Example 4.
-- ||               --   instance (...) => Bin (Mu h a)
-- ||             $ bin_mu_inst
-- ||
-- ||               -- Example 5.
-- ||               --   instance (...) => Bin (HPerfect h a)
-- ||             $ tup_decl
-- ||             $ hperfect_decl
-- ||             $ bin_tup_inst
-- ||             $ bin_hperfect_inst
-- ||
-- ||               -- \x. x
-- ||             $ pexp $ lambda "x" (fvar "x")
-- ||
-- ||
-- ||
-- || -- * Run a test
-- || -- ------------------------------------------------------------------------------
-- ||
-- || start_test :: IO ()
-- || start_test = compile_chatty paper_tests >> putStrLn "\n"
-- ||
-- ||
