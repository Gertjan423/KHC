{-|
Module      : Optimizer.FcTypes
Description : Functions used to pre
Copyright   : Elias Storme, 2021
              Gert-Jan Bottu, 2021

Various 
-}
module Optimizer.FcPreprocessor (bindFreeOptTyVars, mergeAppAbsOptProg) where

import Optimizer.FcTypes
import Utils.FreeVars (ftyvsOf)

-- | Wrap program term in a type abstraction binding its free type variables 
-- (solves bug in the HsTypeChecker which loses track of some type variables)
bindFreeOptTyVars :: FcOptProgram -> FcOptProgram
bindFreeOptTyVars (FcPgmDataDecl decl pgm) = FcPgmDataDecl decl (bindFreeOptTyVars pgm)
bindFreeOptTyVars (FcPgmValDecl  bind pgm) = FcPgmValDecl bind (bindFreeOptTyVars pgm)
bindFreeOptTyVars (FcPgmTerm tm)           = case ftyvsOf tm of
  [] -> FcPgmTerm tm
  as -> FcPgmTerm (FcOptTmTyAbs as tm)

-- | Merge applications and abstractions in an optimizer program
-- | examples:
-- |   \[x].\[y].t becomes \[x,y].t
-- |   (t1 [t2]) [t3] becomes t1 [t2, t3]
-- |   /\[a]./\[b].t becomes /\[a,b].t
-- |   t [ty1] [ty2] becomes t [ty1,ty2]
mergeAppAbsOptProg :: FcOptProgram -> FcOptProgram
mergeAppAbsOptProg (FcPgmDataDecl decl pgm) = FcPgmDataDecl decl (mergeAppAbsOptProg pgm)
mergeAppAbsOptProg (FcPgmValDecl  bind pgm) = FcPgmValDecl (mergeAppAbsOptBind bind) (mergeAppAbsOptProg pgm)
mergeAppAbsOptProg (FcPgmTerm tm) = FcPgmTerm (mergeAppAbsOptTm tm)

-- | Merge applications and abstractions
mergeAppAbsOptTm :: FcOptTerm -> FcOptTerm
-- ^ if the nested term is also an abstraction, append variables at the back
mergeAppAbsOptTm (FcOptTmAbs vs tm) = case mergeAppAbsOptTm tm of
  (FcOptTmAbs vs' tm') -> FcOptTmAbs (vs++vs') tm'
  tm'                  -> FcOptTmAbs vs tm'
-- ^ if the nested term is also an application, append terms at the FRONT
mergeAppAbsOptTm (FcOptTmApp tm tms) = case mergeAppAbsOptTm tm of
  (FcOptTmApp tm' tms') -> FcOptTmApp tm' (tms' ++ map mergeAppAbsOptTm tms)
  tm'                   -> FcOptTmApp tm' (map mergeAppAbsOptTm tms)
-- ^ if the nested term is also a type abstraction, append type variables at the back
mergeAppAbsOptTm (FcOptTmTyAbs as tm) = case mergeAppAbsOptTm tm of
  (FcOptTmTyAbs as' tm') -> FcOptTmTyAbs (as++as') tm'
  tm'                    -> FcOptTmTyAbs as tm'
-- ^ if the nested term is also an application, append types at the FRONT
mergeAppAbsOptTm (FcOptTmTyApp tm tys) = case mergeAppAbsOptTm tm of
  (FcOptTmTyApp tm' tys') -> FcOptTmTyApp tm' (tys'++tys)
  tm'                     -> FcOptTmTyApp tm' tys
-- ^ recursively merge in binding and term
mergeAppAbsOptTm (FcOptTmLet bind tm)  = FcOptTmLet (mergeAppAbsOptBind bind) (mergeAppAbsOptTm tm)
-- ^ recursively merge in scrutinee and alternatives
mergeAppAbsOptTm (FcOptTmCase tm alts) = FcOptTmCase (mergeAppAbsOptTm tm) (mergeAppAbsOptAlts alts)
-- ^ all other terms do not need to recurse, since they do not contain nested terms
mergeAppAbsOptTm tm = tm

-- | Merge applications and abstractions in a binding
mergeAppAbsOptBind :: FcOptBind -> FcOptBind
-- ^ just merge in nested term
mergeAppAbsOptBind (FcBind x ty tm) = FcBind x ty (mergeAppAbsOptTm tm)

-- | Merge applications and abstractions in alternatives
-- | just map mergeAppAbsOptTm over all nested terms in the alts
mergeAppAbsOptAlts :: FcOptAlts -> FcOptAlts
mergeAppAbsOptAlts (FcAAlts alts) = FcAAlts $ map mergeAppAbsOptAAlt alts
  where mergeAppAbsOptAAlt (FcAAlt pat tm) = FcAAlt pat (mergeAppAbsOptTm tm)
mergeAppAbsOptAlts (FcPAlts alts) = FcPAlts $ map mergeAppAbsOptPAlt alts
  where mergeAppAbsOptPAlt (FcPAlt lit tm) = FcPAlt lit (mergeAppAbsOptTm tm)