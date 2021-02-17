data Nil = Nil

class Fst a :: * where
  fst :: forall (b :: *). forall (c :: *). b -> c -> b
class Snd a :: * where  
  snd :: forall (b :: *). forall (c :: *). b -> c -> c
class Loop a :: * where  
  loop :: a

instance Fst Nil where
  fst = \x. \y. x
instance Snd Nil where
  snd = \x. \y. y
instance Loop Nil where
  loop = loop

(fst (\x. x) loop)