module Optimizer.FcPreprocessor where

import Optimizer.FcTypes
import 

FcPreM = UniqueSupplyT (ExceptT String (Writer Trace))

procProgram :: FcOptProgram -> FcPreM FcPreProgram
procProgram (FcPgmDataDecl decl pgm) = FcPgmDataDecl decl <$> (procProgram pgm)
procProgram (FcPgmValDecl  bind pgm) = FcPgmValDecl <$> (procBind bind) <*> (procProgram pgm)
procProgram (FcPgmTerm     tm      ) = FcPgmTerm <$> (procTm tm)

procTm :: FcOptTerm -> FcPreM FcOptTerm
procTm (FcOptTmApp tm1 tms) = procTm tm1 >>= \case
  (FcOptTmApp tm2 tms') -> FcOptTmApp tm2 <*> (mapM procTm (tms' ++ tms))
  tm2                   -> FcOptTmApp tm2 <*> (mapM procTm tms)
procTm (FcOptTmTyApp tm tys1) = procTm tm >>= \case
  (FcOptTmTyApp tm' tys2) -> return FcOptTmTyApp tm' (tys2 ++ tys1)
  tm'                     -> return FcOptTmTyApp tm' tys1
procTm (FcOptTmAbs xs tys1 tm) = procTm tm >>= \case
  (FcOptTmAbs ys tys2 tm') -> FcOptTmAbs (ys ++ xs) (tys2 ++ tys1)
procTm tm = return tm


fcPreProcess :: UniqueSupply -> FcOptProgram -> (Either String (FcPreProgram, UniqueSupply))
fcPreProcess us pgm = runWriter
                    $ runExceptT
                    $ flip runUniqueSupplyT us
                    $ procProgram pgm

