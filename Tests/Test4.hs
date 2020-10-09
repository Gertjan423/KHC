data Nat = Zero | Succ Nat

class One a :: * where
  one :: a

class Two a :: * where
  two :: a

class Add a :: * where
  add :: a -> a -> a

class Sub a :: * where
  sub :: a -> a -> a

class Fib a :: * where
  fib :: a -> a

instance One Nat where
  one = Succ Zero

instance Two Nat where
  two = Succ (Succ Zero)

instance Add Nat where
  add = \n1. \n2. case n2 of
                     Succ n -> add (Succ n1) n
                     Zero   -> n1

instance Sub Nat where
  sub = \n1. \n2. case n1 of
                     Zero     -> Zero
                     Succ n1' -> case n2 of
                                  Zero     -> Succ n1'
                                  Succ n2' -> sub n1' n2'

instance Fib Nat where
  fib = \n. case n of
              Zero -> one
              Succ n' -> case n' of
                            Zero -> one
                            Succ n'' -> add (fib n') (fib n'')

fib (Succ (Succ (Succ (Succ Zero))))