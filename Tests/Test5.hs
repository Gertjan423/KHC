-- * Simple test for using primitives
-- ----------------------------------------------------------------------------

data Bool = True | False

f :: Bool -> Int#
  = \x. case x of
  	True -> 1
  	False -> 2

+# (f True) (f False)