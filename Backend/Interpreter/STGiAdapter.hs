{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Backend.Interpreter.STGiAdapter (stgToStg,runSTGI) where

import Data.Map (singleton)
import Data.List.NonEmpty (fromList)
import Data.Text (pack)

import qualified Stg.Language as STGI
import qualified Stg.Language.Prettyprint as SPP
import Stg.Machine.Types (StgState)
import Stg.RunForPager
import Backend.STGTypes
import Utils.Var (SVar)
import Utils.Prim (PrimLit (..), PrimOp (..), PrimIntOp (..))
import Utils.PrettyPrint (render, ppr)

stgToStg :: SProg -> STGI.Program
stgToStg (SProg binds) = STGI.Program $ bindsToBinds binds

bindsToBinds :: [SBind] -> STGI.Binds
bindsToBinds ((SBind x lf):binds) = (STGI.Binds $ singleton (varToVar x) (lambdaToLambda lf)) <> (bindsToBinds binds)
bindsToBinds [] = mempty

varToVar :: SVar -> STGI.Var
varToVar x = STGI.Var $ pack $ render $ ppr x

litToLit :: PrimLit -> STGI.Literal
litToLit (PInt l) = STGI.Literal $ toInteger l

atomToAtom :: SAtom -> STGI.Atom
atomToAtom (SAtVar x) = STGI.AtomVar $ varToVar x
atomToAtom (SAtLit l) = STGI.AtomLit $ litToLit l

ufToUf :: SUFlag -> STGI.UpdateFlag
ufToUf Uble = STGI.Update
ufToUf NUble = STGI.NoUpdate

lambdaToLambda :: SLForm -> STGI.LambdaForm
lambdaToLambda (SLForm xs uf ys e) = STGI.LambdaForm (map varToVar xs) (ufToUf uf) (map varToVar ys) (exprToExpr e)

conToCon :: SCon -> STGI.Constr
conToCon (SCon c) = STGI.Constr $ pack $ render $ ppr c

popToPop :: PrimOp -> STGI.PrimOp
popToPop (PrimIntOp PIntAdd) = STGI.Add
popToPop (PrimIntOp PIntSub) = STGI.Sub
popToPop (PrimIntOp PIntMul) = STGI.Mul

altsToAlts :: SAlts -> STGI.Alts
altsToAlts (SAAlts alts defAlt) = case map aaltToAalt alts of
  [] -> STGI.Alts STGI.NoNonDefaultAlts (daltToDalt defAlt)
  alts' -> STGI.Alts (STGI.AlgebraicAlts $ fromList alts') (daltToDalt defAlt)
altsToAlts (SPAlts alts defAlt) = case map paltToPalt alts of
  [] -> STGI.Alts STGI.NoNonDefaultAlts (daltToDalt defAlt)
  alts' -> STGI.Alts (STGI.PrimitiveAlts $ fromList alts') (daltToDalt defAlt)

aaltToAalt :: SAAlt -> STGI.AlgebraicAlt
aaltToAalt (SAAlt c xs e) = STGI.AlgebraicAlt (conToCon c) (map varToVar xs) (exprToExpr e)

paltToPalt :: SPAlt -> STGI.PrimitiveAlt
paltToPalt (SPAlt l e) = STGI.PrimitiveAlt (litToLit l) (exprToExpr e)

daltToDalt :: SDefAlt -> STGI.DefaultAlt
daltToDalt (SDefBound x e) = STGI.DefaultBound (varToVar x) (exprToExpr e)
daltToDalt (SDefUnbound e) = STGI.DefaultNotBound (exprToExpr e)

exprToExpr :: SExpr -> STGI.Expr
exprToExpr (SLet binds e) = STGI.Let STGI.Recursive (bindsToBinds binds) (exprToExpr e)
exprToExpr (SCase e alts) = STGI.Case (exprToExpr e) (altsToAlts alts)
exprToExpr (SApp  x  ats) = STGI.AppF (varToVar x ) (map atomToAtom ats)
exprToExpr (SCApp c  ats) = STGI.AppC (conToCon c ) (map atomToAtom ats)
exprToExpr (SPApp op ats) = STGI.AppP (popToPop op) (atomToAtom $ head ats) (atomToAtom $ last ats)
exprToExpr (SELit lit   ) = STGI.LitE (litToLit lit)

runSTGI :: STGI.Program -> IO StgState
runSTGI = runForPager richRenderer Nothing 2

richRenderer :: Renderer
richRenderer = Renderer
    { renderProgram   = SPP.renderRich . SPP.prettyStgi
    , renderState     = SPP.renderRich . SPP.prettyStgi
    , renderInfo      = SPP.renderRich . SPP.prettyStgi
    , renderInfoShort = SPP.renderRich . SPP.prettyStgi
    }