module Optimizer.FcPreprocessor (mergeAppAbsOptProg) where

import Optimizer.FcTypes

mergeAppAbsOptProg :: FcOptProgram -> FcOptProgram
mergeAppAbsOptProg (FcPgmDataDecl decl pgm) = FcPgmDataDecl decl (mergeAppAbsOptProg pgm)
mergeAppAbsOptProg (FcPgmValDecl  bind pgm) = FcPgmValDecl (mergeAppAbsOptBind bind) (mergeAppAbsOptProg pgm)
mergeAppAbsOptProg (FcPgmTerm tm) = FcPgmTerm (mergeAppAbsOptTm tm)

-- | Merge applications and abstractions
mergeAppAbsOptTm :: FcOptTerm -> FcOptTerm
mergeAppAbsOptTm (FcOptTmAbs vs tm) = case mergeAppAbsOptTm tm of
  (FcOptTmAbs vs' tm') -> FcOptTmAbs (vs++vs') tm'
  tm'                  -> FcOptTmAbs vs tm'
mergeAppAbsOptTm (FcOptTmApp tm tms) = case mergeAppAbsOptTm tm of
  (FcOptTmApp tm' tms') -> FcOptTmApp tm' (tms' ++ map mergeAppAbsOptTm tms)
  tm'                   -> FcOptTmApp tm' (map mergeAppAbsOptTm tms)
mergeAppAbsOptTm (FcOptTmTyAbs as tm) = case mergeAppAbsOptTm tm of
  (FcOptTmTyAbs as' tm') -> FcOptTmTyAbs (as++as') tm'
  tm'                    -> FcOptTmTyAbs as tm'
mergeAppAbsOptTm (FcOptTmTyApp tm tys) = case mergeAppAbsOptTm tm of
  (FcOptTmTyApp tm' tys') -> FcOptTmTyApp tm' (tys'++tys)
  tm'                     -> FcOptTmTyApp tm' tys
mergeAppAbsOptTm (FcOptTmLet bind tm)  = FcOptTmLet (mergeAppAbsOptBind bind) (mergeAppAbsOptTm tm)
mergeAppAbsOptTm (FcOptTmCase tm alts) = FcOptTmCase (mergeAppAbsOptTm tm) (mergeAppAbsOptAlts alts)
-- ^ all other terms do not need to recurse
mergeAppAbsOptTm tm = tm

mergeAppAbsOptBind :: FcOptBind -> FcOptBind
mergeAppAbsOptBind (FcBind x ty tm) = FcBind x ty (mergeAppAbsOptTm tm)

mergeAppAbsOptAlts :: FcOptAlts -> FcOptAlts
mergeAppAbsOptAlts (FcAAlts alts) = FcAAlts $ map mergeAppAbsOptAAlt alts
  where mergeAppAbsOptAAlt (FcAAlt pat tm) = FcAAlt pat (mergeAppAbsOptTm tm)
mergeAppAbsOptAlts (FcPAlts alts) = FcPAlts $ map mergeAppAbsOptPAlt alts
  where mergeAppAbsOptPAlt (FcPAlt lit tm) = FcPAlt lit (mergeAppAbsOptTm tm)