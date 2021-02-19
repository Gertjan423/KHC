module Utils.Prim (PrimTy(..), PrimTm(..), PrimOp(..), PrimLit(..)) where

import Utils.PrettyPrint

data PrimTy = PIntTy

data PrimTm = PrimOpTm PrimOp | PrimLitTm PrimLit

data PrimOp = PIntAdd 
            | PIntSub
            | PIntMul
            | PIntEq

newtype PrimLit = PInt Int

instance PrettyPrint PrimTy where
  ppr PIntTy = text "Int#"
  needsParens _ = False

instance PrettyPrint PrimTm where
  ppr (PrimOpTm x)  = ppr x
  ppr (PrimLitTm x) = ppr x
  needsParens _ = False

instance PrettyPrint PrimOp where
  ppr PIntAdd = text "+#"
  ppr PIntSub = text "-#"
  ppr PIntMul = text "*#"
  ppr PIntEq  = text "==#"
  needsParens _ = False

instance PrettyPrint PrimLit where
  ppr (PInt x) = ppr x <> text "#"
  needsParens _ = False