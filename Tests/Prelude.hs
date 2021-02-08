-- | Description : Prelude adapted for KHC
-- | Copyright   : ???

-- General/Miscellaneous functions
id :: forall (a :: *).
      a -> a
    = \x.x

const :: forall (a :: *).
         forall (b :: *).
         a -> b -> a
       = \x.\y.x

compose :: forall (a :: *). -- f . g
           forall (b :: *).
           forall (c :: *).
           (b -> c) -> (a -> b) -> a -> c
         = \f.\g.\x. f (g x)

flip :: forall (a :: *).
        forall (b :: *).
        forall (c :: *).
        (a -> b -> c) -> b -> a -> c
      = \f.\x.\y. f y x

apply :: forall (a :: *). -- f $ x
         forall (b :: *).
         (a -> b) -> a -> b
       = id

asTypeOf :: forall (a :: *).
            a -> a -> a
          = const

undefined :: forall (a :: *). a = undefined

-- Bool
data Bool = True | False

if' :: forall (a :: *).
      Bool -> a -> a -> a
    = \c.\t.\f. case c of
                  True  -> t
                  False -> f

b_and :: Bool -> Bool -> Bool -- binary and &&
       = \x. if' x id (const False)

b_or :: Bool -> Bool -> Bool -- binary or ||
      = \x. if' x (const True) id

not :: Bool -> Bool
     = \x. if' x False True

otherwise :: Bool = True

until :: forall (a :: *).
         (a -> Bool) -> (a -> a) -> a -> a
       = \c.\f.\x. if' (c x) x (until c f (f x))

-- Maybe
data Maybe (a :: *) = Nothing | Just a

maybe :: forall (a :: *).
         forall (b :: *).
         b -> (a -> b) -> Maybe a -> b
       = \b.\f.\x. case x of
                     Just a  -> f a
                     Nothing -> b

-- Either
data Either (a :: *) (b :: *) = Left a | Right b

either :: forall (a :: *).
          forall (b :: *).
          forall (c :: *).
          (a -> c) -> (b -> c) -> Either a b -> c
        = \f.\g.\x. case x of
                      Left  a -> f a
                      Right b -> g b

-- Pairs
data Pair (a :: *) (b :: *) = Pair a b

fst :: forall (a :: *).
       forall (b :: *).
       Pair a b -> a
     = \x. case x of
             Pair a b -> a

snd :: forall (a :: *).
       forall (b :: *).
       Pair a b -> b
     = \x. case x of
             Pair a b -> b

curry :: forall (a :: *).
         forall (b :: *).
         forall (c :: *).
         (Pair a b -> c) -> a -> b -> c
       = \f.\a.\b. f (Pair a b)

uncurry :: forall (a :: *).
           forall (b :: *).
           forall (c :: *).
           (a -> b -> c) -> Pair a b -> c
         = \f.\p. f (fst p) (snd p)

-- Eq
class Eq a :: * where
  equals :: a -> a -> Bool -- x == y

notEquals :: forall (a :: *).
             Eq a =>
             a -> a -> Bool
           = \x.\y. not (equals x y)

instance Eq Bool where
  equals = \x. if' x id not

instance Eq a => Eq (Maybe (a :: *)) where
  equals = maybe (maybe True (\w.False))
                 (\x. maybe False (equals x))

instance (Eq a, Eq b) => Eq (Either (a :: *) (b :: *)) where
  equals = either (\a. either (equals a) (const False))
                  (\b. either (const False) (equals b))

instance (Eq a, Eq b) => Eq (Pair (a :: *) (b :: *)) where
  equals = \x.\y. b_and (equals (fst x) (fst y)) (equals (snd x) (snd y))

-- Functor
class Functor f :: * -> * where
  fmap :: forall (a :: *).
          forall (b :: *).
          (a -> b) -> f a -> f b

fmapl :: forall (f :: * -> *). -- a <$ f
         forall (a :: *).
         forall (b :: *).
         Functor f =>
         a -> f b -> f a
       = compose fmap const

instance Functor Maybe where
  fmap = \f. maybe Nothing (compose Just f)

-- Applicative
class Functor f => Applicative f :: * -> * where
  classMethodsApplicative :: forall (a :: *). -- defines pure and seq_apply
                             forall (b :: *).
                             Pair (a -> f a) (f (a -> b) -> f a -> f b)

pure :: forall (f :: * -> *).
        forall (a :: *).
        Applicative f =>
        a -> f a
      = fst classMethodsApplicative

seq_apply :: forall (f :: * -> *). -- m1 <*> m2
             forall (a :: *).
             forall (b :: *).
             Applicative f =>
             f (a -> b) -> f a -> f b
           = snd classMethodsApplicative

seq_applyr :: forall (f :: * -> *). -- m1 <*> m2
              forall (a :: *).
              forall (b :: *).
              Applicative f =>
              f a -> f b -> f b
            = compose seq_apply (fmapl id)

seq_applyl :: forall (f :: * -> *). -- m1 <*> m2
              forall (a :: *).
              forall (b :: *).
              Applicative f =>
              f a -> f b -> f a
            = compose seq_apply (fmap const)

instance Applicative Maybe where
  classMethodsApplicative = Pair Just (maybe (const Nothing) fmap)

-- Monad
class Applicative m => Monad m :: * -> * where
  seq_compose :: forall (a :: *). -- m >>= f
                 forall (b :: *).
                 m a -> (a -> m b) -> m b

instance Monad Maybe where
  seq_compose = \m.\f. maybe Nothing f m

return :: forall (m :: * -> *).
          forall (a :: *).
          Monad m =>
          a -> m a
        = pure

-- Foldable
class Foldable t :: * -> * where
  foldr :: forall (a :: *).
           forall (b :: *).
           (a -> b -> b) -> b -> t a -> b

foldl :: forall (t :: * -> *).
         forall (a :: *).
         forall (b :: *).
         Foldable t =>
         (b -> a -> b) -> b -> t a -> b
       = \f.\b.\t. foldr (\a.\ctx.(\x.ctx (f x a))) id t b

and :: forall (t :: * -> *).
       Foldable t =>
       t Bool -> Bool
     = foldr b_and True

or :: forall (t :: * -> *).
      Foldable t =>
      t Bool -> Bool
    = foldr b_or True

any :: forall (t :: * -> *).
       forall (a :: *).
       Foldable t =>
       (a -> Bool) -> t a -> Bool
     = \f. foldr (\x. if' (f x) True) False

all :: forall (t :: * -> *).
       forall (a :: *).
       Foldable t =>
       (a -> Bool) -> t a -> Bool
     = \f. foldr (\x. flip (if' (f x)) False) True

elem :: forall (t :: * -> *).
        forall (a :: *).
        Foldable t => Eq a =>
        a -> t a -> Bool
      = \x. any (equals x)

instance Foldable Maybe where
  foldr = \f.\b. maybe b (flip f b)

-- List
data List (a :: *) = Nil | Cons a (List a)

map :: forall (a :: *).
       forall (b :: *).
       (a -> b) -> List a -> List b
     = \f.\xs. case xs of
                 Cons y ys -> Cons (f y) (map f ys)
                 Nil       -> Nil

append :: forall (a :: *). -- xs ++ ys
          List a -> List a -> List a
        = \xs. case xs of
                 Cons y ys -> compose (Cons y) (append ys)
                 Nil       -> id

filter :: forall (a :: *).
          (a -> Bool) -> List a -> List a
        = \f.\xs. case xs of
                    Cons y ys -> if' (f y) (Cons y) id (filter f ys)
                    Nil       -> Nil

null :: forall (a :: *).
        List a -> Bool
      = \xs. case xs of
               Cons y ys -> False
               Nil       -> True

head :: forall (a :: *).
        List a -> a
      = \xs. case xs of
               Cons y ys -> y

tail :: forall (a :: *).
        List a -> List a
      = \xs. case xs of
               Cons y ys -> ys

last :: forall (a :: *).
        List a -> a
      = \xs. case xs of
               Cons y ys -> if' (null ys) y (last ys)

init :: forall (a :: *).
        List a -> List a
      = \xs. case xs of
               Cons y ys -> if' (null ys) Nil (Cons y (init ys))

concatMap :: forall (t :: * -> *).
             forall (a :: *).
             forall (b :: *).
             Foldable t =>
             (a -> List b) -> t a -> List b
           = \f. foldr (compose append f) Nil

concat :: forall (t :: * -> *).
          forall (a :: *).
          Foldable t =>
          t (List a) -> List a
        = concatMap id

scanl :: forall (a :: *).
         forall (b :: *).
         (b -> a -> b) -> b -> List a -> List b
       = \f.\b.\xs. Cons b (if' (null xs) Nil (scanl f (f b (head xs)) (tail xs)))

scanr :: forall (a :: *).
         forall (b :: *).
         (a -> b -> b) -> b -> List a -> List b
       = \f.\b.\xs. let qs = scanr f b (tail xs)
                    in  if' (null xs) (Cons b Nil) (Cons (f (head xs) (head qs)) qs)

iterate :: forall (a :: *).
           (a -> a) -> a -> List a
         = \f.\x. Cons x (iterate f (f x))

repeat :: forall (a :: *).
          a -> List a
        = \x. let xs = Cons x xs in xs

cycle :: forall (a :: *).
         List a -> List a
       = \xs. let ys = append xs ys in ys

dropWhile :: forall (a :: *).
             (a -> Bool) -> List a -> List a
           = \f.\xs. case xs of
                       Cons y ys -> if' (f y) (dropWhile f ys) ys
                       Nil       -> Nil

takeWhile :: forall (a :: *).
             (a -> Bool) -> List a -> List a
           = \f.\xs. case xs of
                       Cons y ys -> if' (f y) (Cons y (takeWhile f ys)) Nil
                       Nil       -> Nil

zip :: forall (a :: *).
       forall (b :: *).
       List a -> List b -> List (Pair a b)
     = \xs.\ys. if' (b_or (null xs) (null ys))
                    (Nil)
                    (Cons (Pair (head xs) (head ys)) (zip (tail xs) (tail ys)))

instance Eq a => Eq (List (a :: *)) where
  equals = \xs.\ys. if' (null xs) (null ys) (b_and (not (null ys))
                                                   (b_and (equals (head xs) (head ys))
                                                          (equals (tail xs) (tail ys))))

instance Foldable List where
  foldr = \f.\b.\xs. case xs of
                       Cons y ys -> f y (foldr f b ys)
                       Nil       -> b

instance Functor List where
  fmap = map

instance Applicative List where
  classMethodsApplicative = Pair (flip Cons Nil) (\fs.\xs. concatMap (\f. map f xs) fs)

instance Monad List where
  seq_compose = flip concatMap

reverse :: forall (a :: *).
           List a -> List a
         = foldl (flip Cons) Nil

-- Ordering
data Ordering = LT | EQ | GT

instance Eq Ordering where
  equals = \x.\y. case x of
                    LT -> case y of
                            LT -> True
                            EQ -> False
                            GT -> False
                    EQ -> case y of
                            LT -> False
                            EQ -> True
                            GT -> False
                    GT -> case y of
                            LT -> False
                            EQ -> False
                            GT -> True

-- Ord
class Eq a => Ord a :: * where
  compare :: a -> a -> Ordering

isLT :: forall (a :: *).
        Ord a =>
        a -> a -> Bool
      = \x.\y. equals (compare x y) LT

isLE :: forall (a :: *).
        Ord a =>
        a -> a -> Bool
      = \x.\y. notEquals (compare x y) GT

isGT :: forall (a :: *).
        Ord a =>
        a -> a -> Bool
      = \x.\y. equals (compare x y) GT

isGE :: forall (a :: *).
        Ord a =>
        a -> a -> Bool
      = \x.\y. notEquals (compare x y) LT

instance Ord Bool where
  compare = \x.\y. if' x (if' y EQ GT) (if' y LT EQ)

instance Ord a => Ord (Maybe (a :: *)) where
  compare = maybe (maybe EQ (const LT))
                  (\a. maybe GT (compare a))

instance (Ord a, Ord b) => Ord (Either (a :: *) (b :: *)) where
  compare = either (\a. either (compare a) (const LT))
                   (\b. either (const GT) (compare b))

instance Ord Ordering where
  compare = \x.\y. case x of
                     LT -> case y of
                             LT -> EQ
                             EQ -> GT
                             GT -> GT
                     EQ -> case y of
                             LT -> LT
                             EQ -> EQ
                             GT -> GT
                     GT -> case y of
                             LT -> LT
                             EQ -> LT
                             GT -> GT

instance (Ord a, Ord b) => Ord (Pair (a :: *) (b :: *)) where
  compare = \x.\y. case compare (fst x) (fst y) of
                     LT -> LT
                     EQ -> compare (snd x) (snd y)
                     GT -> GT

-- Semigroup
class Semigroup a :: * where
  mappend :: a -> a -> a

instance Semigroup (List (a :: *)) where
  mappend = append

instance (Semigroup a, Semigroup b) => Semigroup (Pair (a :: *) (b :: *)) where
  mappend = \x.\y. Pair (mappend (fst x) (fst y)) (mappend (snd x) (snd y))

-- Integer
data Digit = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9 -- decimal digits

digitCompare :: Digit -> Digit -> Ordering
              = \x.\y. case x of
                          D0 -> case y of
                                  D0 -> EQ
                                  D1 -> LT
                                  D2 -> LT
                                  D3 -> LT
                                  D4 -> LT
                                  D5 -> LT
                                  D6 -> LT
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D1 -> case y of
                                  D0 -> GT
                                  D1 -> EQ
                                  D2 -> LT
                                  D3 -> LT
                                  D4 -> LT
                                  D5 -> LT
                                  D6 -> LT
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D2 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> EQ
                                  D3 -> LT
                                  D4 -> LT
                                  D5 -> LT
                                  D6 -> LT
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D3 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> EQ
                                  D4 -> LT
                                  D5 -> LT
                                  D6 -> LT
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D4 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> GT
                                  D4 -> EQ
                                  D5 -> LT
                                  D6 -> LT
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D5 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> GT
                                  D4 -> GT
                                  D5 -> EQ
                                  D6 -> LT
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D6 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> GT
                                  D4 -> GT
                                  D5 -> GT
                                  D6 -> EQ
                                  D7 -> LT
                                  D8 -> LT
                                  D9 -> LT
                          D7 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> GT
                                  D4 -> GT
                                  D5 -> GT
                                  D6 -> GT
                                  D7 -> EQ
                                  D8 -> LT
                                  D9 -> LT
                          D8 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> GT
                                  D4 -> GT
                                  D5 -> GT
                                  D6 -> GT
                                  D7 -> GT
                                  D8 -> EQ
                                  D9 -> LT
                          D9 -> case y of
                                  D0 -> GT
                                  D1 -> GT
                                  D2 -> GT
                                  D3 -> GT
                                  D4 -> GT
                                  D5 -> GT
                                  D6 -> GT
                                  D7 -> GT
                                  D8 -> GT
                                  D9 -> EQ

instance Eq Digit where
  equals = \x.\y. equals (digitCompare x y) EQ

instance Ord Digit where
  compare = digitCompare

data Integer = Integer Bool (List Digit) -- sign (True = positive) and digits (list of igits in decreasing significance, the way you would write them normally)

natural :: List Digit -> Integer -- convrts a digit list to a number
         = Integer True

digit :: Digit -> Integer -- converts a single igit to a number
       = compose natural pure

zero :: Integer = natural Nil -- 0

one :: Integer = digit D1  -- 1

signBool :: Integer -> Bool -- returns True for strictly positive numbers, False for strictly negative numbers and either True or False for 0
          = \x. case x of
                  Integer s w -> s

prependToUnifyLengths :: forall (a :: *). -- Prepends the least amount of elements to the lists so that they have the same length (used to ge the same amont of igits in a number before addition)
                         forall (b :: *).
                         a -> b -> List a -> List b -> Pair (List a) (List b)
                       = \a.\b.\as.\bs. if' (null as)
                                            (if' (null bs)
                                                 (Pair Nil Nil)
                                                 (Pair (map (const a) bs) bs))
                                            (if' (null bs)
                                                 (Pair as (map (const b) as))
                                                 (mappend (prependToUnifyLengths a b (init as) (init bs))
                                                          (Pair (pure (last as)) (pure (last bs)))))

addDigit :: Digit -> Digit -> Pair Digit Digit -- Add single digits (gives 2 digits)
          = \x.\y. if' (equals (compare x y) GT)
                       (addDigit y x)
                       (case x of
                          D0 -> Pair D0 y
                          D1 -> case y of
                                  D1 -> Pair D0 D2
                                  D2 -> Pair D0 D3
                                  D3 -> Pair D0 D4
                                  D4 -> Pair D0 D5
                                  D5 -> Pair D0 D6
                                  D6 -> Pair D0 D7
                                  D7 -> Pair D0 D8
                                  D8 -> Pair D0 D9
                                  D9 -> Pair D1 D0
                          D2 -> case y of
                                  D2 -> Pair D0 D4
                                  D3 -> Pair D0 D5
                                  D4 -> Pair D0 D6
                                  D5 -> Pair D0 D7
                                  D6 -> Pair D0 D8
                                  D7 -> Pair D0 D9
                                  D8 -> Pair D1 D0
                                  D9 -> Pair D1 D1
                          D3 -> case y of
                                  D3 -> Pair D0 D6
                                  D4 -> Pair D0 D7
                                  D5 -> Pair D0 D8
                                  D6 -> Pair D0 D9
                                  D7 -> Pair D1 D0
                                  D8 -> Pair D1 D1
                                  D9 -> Pair D1 D2
                          D4 -> case y of
                                  D4 -> Pair D0 D8
                                  D5 -> Pair D0 D9
                                  D6 -> Pair D1 D0
                                  D7 -> Pair D1 D1
                                  D8 -> Pair D1 D2
                                  D9 -> Pair D1 D3
                          D5 -> case y of
                                  D5 -> Pair D1 D0
                                  D6 -> Pair D1 D1
                                  D7 -> Pair D1 D2
                                  D8 -> Pair D1 D3
                                  D9 -> Pair D1 D4
                          D6 -> case y of
                                  D6 -> Pair D1 D2
                                  D7 -> Pair D1 D3
                                  D8 -> Pair D1 D4
                                  D9 -> Pair D1 D5
                          D7 -> case y of
                                  D7 -> Pair D1 D4
                                  D8 -> Pair D1 D5
                                  D9 -> Pair D1 D6
                          D8 -> case y of
                                  D8 -> Pair D1 D6
                                  D9 -> Pair D1 D7
                          D9 -> Pair D1 D8 )

digitComplement :: Digit -> Digit -- (10 - the digit) mod 10
                 = \x. case x of
                         D0 -> D0
                         D1 -> D9
                         D2 -> D8
                         D3 -> D7
                         D4 -> D6
                         D5 -> D5
                         D6 -> D4
                         D7 -> D3
                         D8 -> D2
                         D9 -> D1

subDigit :: Digit -> Digit -> Pair Digit Digit -- subtract single digits (first digit is 0 if the result is positive and 1 if it is negative, second digit is he difference mod 10)
          = \x.\y. if' (equals (compare x y) LT)
                       (Pair D1 (snd (subDigit y x)))
                       (Pair D0 (snd (addDigit x (digitComplement y))))

trimDigits :: List Digit -> List Digit -- remove leading zeros
            = dropWhile (equals D0)

instance Eq Integer where
  equals = \x.\y. case x of
                    Integer sx dsx -> case y of
                                        Integer sy dsy -> let dsx' = trimDigits dsx
                                                          in  let dsy' = trimDigits dsy
                                                              in  if' (null dsx')
                                                                      (null dsy')
                                                                      (b_and (equals sx sy)
                                                                             (equals dsx' dsy'))

addDigits :: List Digit -> List Digit -> List Digit -- add digit lists of 2 natural numbers
           = let f = \xs.\ys. if' (null xs)
                                  (Cons D0 Nil)
                                  (let zs = f (tail xs) (tail ys)
                                   in  let xz = addDigit (head xs) (head zs)
                                       in  let xys1 = addDigit (head ys) (snd xz)
                                           in  let xys2 = addDigit (fst xz) (fst xys1)
                                               in  Cons (snd xys2) (Cons (snd xys1) (tail zs)))
             in  \xs.\ys. trimDigits (uncurry f (prependToUnifyLengths D0 D0 xs ys))

subDigits :: List Digit -> List Digit -> Pair Bool (List Digit) -- subtract digit lists of 2 natural numbers
           = let f = \xs.\ys. if' (null xs)
                                  (Cons D0 Nil)
                                  (let zs = f (tail xs) (tail ys)
                                   in  let xz = subDigit (head xs) (head zs)
                                       in  let xys1 = subDigit (head ys) (snd xz)
                                           in  let xys2 = addDigit (fst xz) (fst xys1)
                                               in  Cons (snd xys2) (Cons (snd xys1) (tail zs)))
             in  \xs.\ys. let zs = uncurry f (prependToUnifyLengths D0 D0 xs ys)
                          in  Pair (equals (head zs) D0) (trimDigits (tail zs))

add :: Integer -> Integer -> Integer -- x + y
     = \x.\y. case x of
                Integer sx dsx -> case y of
                                    Integer sy dsy -> if' (equals sx sy)
                                                          (Integer sx (addDigits dsx dsy))
                                                          (let diff = subDigits dsx dsy
                                                           in  Integer (equals (fst diff) sx)
                                                                       (snd diff))

negate :: Integer -> Integer -- -x
        = \x. case x of
                Integer s ds -> Integer (not s) ds

subtract :: Integer -> Integer -> Integer -- x - y
          = \x.\y. add x (negate y)

-- main = sum [0..9]
(let ds = Cons D0 (Cons D1 (Cons D2 (Cons D3 (Cons D4
          (Cons D5 (Cons D6 (Cons D7 (Cons D8 (Cons D9 Nil)))))))))
 in  foldr add zero (map digit ds))
