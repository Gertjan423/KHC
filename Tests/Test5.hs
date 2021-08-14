-- * Simple test for using primitives
-- ----------------------------------------------------------------------------

data Int = Int Int#

case Int (-# (+# 2 4) 4) of
  Int v -> Int v