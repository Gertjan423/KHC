
module Utils.Kind (Kind(..), Kinded(..), mkArrowKind) where

import Utils.PrettyPrint

-- * Kinds
-- ------------------------------------------------------------------------------

data Kind = KStar | KArr Kind Kind
  deriving (Eq)

instance PrettyPrint Kind where
  ppr KStar        = colorDoc yellow (text "*")
  ppr (KArr k1 k2) = pprPar k1 <+> arrow <+> pprPar k2

  needsParens KStar     = False
  needsParens (KArr {}) = True

-- | Create an arrow kind (uncurried)
mkArrowKind :: [Kind] -> Kind -> Kind
mkArrowKind arg_kinds res_kind = foldr KArr res_kind arg_kinds

-- * The Kinded Class: Everything we can get a Kind out of
-- ------------------------------------------------------------------------------

class Kinded a where
  kindOf :: a -> Kind
