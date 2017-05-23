
-- * Example By Steven Keuchel, related to Okasaki's Square Matrices
-- ----------------------------------------------------------------------------

data Nil (a :: *) = Nil

data Cons (n :: * -> *) (a :: *) = Cons a (n a)

data Square' (c :: (* -> *) -> (* -> *)) (n :: * -> *) (a :: *)
  =  Zero (n (n a)) | Succ (Square' c (c n) a)

-- | Booleans
data Bool = True | False

-- | Simplified Eq class
class () => Eq (a :: *) where {
  eq :: a -> a -> Bool
}

-- instance Eq a => Eq (Nil a)
instance (Eq a) => Eq (Nil (a :: *)) where {
  eq = \n. \m. case n of {
    Nil -> case m of {
      Nil -> True
    }
  }
}

-- instance Eq Bool
instance () => Eq Bool where {
  eq = \a. \b. case a of
                 { True  -> case b of
                              { True  -> True
                              ; False -> False }
                 ; False -> case b of
                              { True  -> False
                              ; False -> True }
                 }
}

-- instance (forall b. Eq b => Eq (f b), Eq a) => Eq (Cons f a)
instance (Eq a, forall (b :: *). Eq b => Eq (f b)) => Eq (Cons (f :: * -> *) (a :: *)) where {
  eq = let { and = \a. \b. case a of
               { True  -> case b of
                  { True  -> True
                  ; False -> False }
               ; False -> False
               }}
       in \n. \m. case n of {
                    Cons x xs -> case m of {
                      Cons y ys -> and (eq x y) (eq xs ys)
                  }}
}


-- instance ( forall m b.
--              (forall e. Eq e => Eq (m e)) =>
--              Eq b => Eq (c m b)
--          , forall b.
--              Eq b => Eq (n b)
--          , Eq a
--          ) => Eq (Square' c n a)
instance ( Eq a
         , forall (b :: *). Eq b => Eq (n b)
         , forall (m :: * -> *). forall (b :: *). (forall (e :: *). Eq e => Eq (m e)) => Eq b => Eq (c m b)
         ) => Eq (Square' (c :: (* -> *) -> * -> *) (n :: * -> *) (a :: *)) where {
  eq = \a. \b. case a of
                 { Zero x -> case b of
                               { Zero y -> eq x y
                               ; Succ z -> False }
                 ; Succ x -> case b of
                               { Zero z -> False
                               ; Succ y -> eq x y }
                 }
}

-- | Program expression
eq (Succ (Succ (Zero
      (Cons (Cons True  (Cons False Nil))
      (Cons (Cons False (Cons True  Nil))
       Nil)))))
   (Succ (Succ (Succ (Zero
         (Cons (Cons True  (Cons False (Cons True  Nil)))
         (Cons (Cons False (Cons True  (Cons False Nil)))
         (Cons (Cons True  (Cons False (Cons True  Nil)))
          Nil)))))))
