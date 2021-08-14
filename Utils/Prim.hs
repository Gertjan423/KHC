{-|
Module      : Utils.Prim
Description : Datatypes for primitive terms
Copyright   : Elias Storme, 2020
              Gert-Jan Bottu, 2020

Datatypes for primitive operators and literals used throughout the compiler
-}
module Utils.Prim where

import Utils.PrettyPrint

-- | Primitive term
data PrimTm = PrimOpTm PrimOp    -- ^ Operator
            | PrimLitTm PrimLit  -- ^ Literal
  deriving Eq

-- | Primitive operator
newtype PrimOp = PrimIntOp PrimIntOp
  deriving Eq

-- | Primitive operator on integers
data PrimIntOp = PIntAdd 
               | PIntSub
               | PIntMul
               -- | PIntEq
  deriving Eq

-- | Primitive literal
newtype PrimLit = PInt Int -- ^ Integer literal
  deriving Eq

--
-- Pretty Printing
--

instance PrettyPrint PrimTm where
  ppr (PrimOpTm x)  = ppr x
  ppr (PrimLitTm x) = ppr x
  needsParens _ = False

instance PrettyPrint PrimOp where
  ppr (PrimIntOp x) = ppr x
  needsParens _ = False

instance PrettyPrint PrimIntOp where
  ppr PIntAdd = text "plus#"
  ppr PIntSub = text "minus#"
  ppr PIntMul = text "mul#"
  -- ppr PIntEq  = text "==#"
  needsParens _ = False

instance PrettyPrint PrimLit where
  ppr (PInt x) = ppr x <> text "#"
  needsParens _ = False