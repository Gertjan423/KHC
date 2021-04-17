-- * Simple test for using primitives
-- ----------------------------------------------------------------------------

data Bool = True | False

f :: Int# -> Int#
  = \x. case x of
  	2 -> -8
  	5 -> 2

-# (+# 1 (f 2)) (*# (f 4) (f 8))