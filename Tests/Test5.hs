-- * Simple test for using primitives
-- ----------------------------------------------------------------------------

data Bool = True | False

f :: Bool -> Int#
  = \x. case x of
  	True -> -8
  	False -> 2

-# (+# 1 (f False)) (*# (f True) (f False))