module Optimizer.FcOptimizer where

import Utils.AssocList

-- | Data constructor environment, listing type variables for type and data constructors
type DCEnv = (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)

type FcOptM = UniqueSupplyT 

type FcOptPass = DCEnv -> UniqueSupply -> FcOptProgram -> 