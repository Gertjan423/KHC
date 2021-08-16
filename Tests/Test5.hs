-- * Fibonnaci implemented using primitives
-- ----------------------------------------------------------------------------

fib :: Int# -> Int#
  = \n. case n of
    0 -> 1
    1 -> 1
    n' -> +# (fib (-# n' 1)) (fib (-# n' 2))

(fib 5)