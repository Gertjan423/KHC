{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}

module Optimizer.FcTypeChecker (fcOptElaborate, fcResElaborate) where

import Optimizer.FcTypes
import Backend.STGTypes

import Utils.AssocList
import Utils.Ctx
import Utils.Errors
import Utils.FreeVars (ftmvsOf)
import Utils.Kind
import Utils.PrettyPrint
import Utils.Prim
import Utils.Substitution
import Utils.Trace
import Utils.Unique
import Utils.Utils
import Utils.Var

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Bifunctor (first, second, bimap)
import Data.List ((\\))

-- * Type checking monad
-- ----------------------------------------------------------------------------
type FcM = UniqueSupplyT (ReaderT FcCtx (StateT FcGblEnv (ExceptT String (Writer Trace))))

type FcCtx = Ctx FcTmVar FcType FcTyVar Kind

-- * Lookup things in the global environment
-- ----------------------------------------------------------------------------

-- | Lookup something in the global environment
lookupFcGblEnvM :: (Eq a, PrettyPrint a, MonadError String m, MonadState s m) => (s -> AssocList a b) -> a -> m b
lookupFcGblEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> throwErrorM (text "lookupFcGblEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup the info of a type constructor
lookupTyConInfoM :: FcTyCon -> FcM FcTyConInfo
lookupTyConInfoM = lookupFcGblEnvM fc_env_tc_info

-- | Lookup the kind of a type constructor
lookupTyConKindM :: FcTyCon -> FcM Kind
lookupTyConKindM tc = foldr (KArr . kindOf) KStar . fc_tc_type_args
  <$> lookupTyConInfoM tc

-- | Lookup the info of a data constructor
lookupDataConInfoM :: FcDataCon -> FcM FcDataConInfo
lookupDataConInfoM = lookupFcGblEnvM fc_env_dc_info

-- | Lookup the type of a data constructor
lookupDataConTyM :: FcDataCon -> FcM ([FcTyVar], [FcType], FcTyCon)
lookupDataConTyM dc = lookupDataConInfoM dc >>= \info ->
  return (fc_dc_univ info, fc_dc_arg_tys info, fc_dc_parent info)

-- * Ensure that some things are not bound in the local context
-- ----------------------------------------------------------------------------

-- | Ensure something is unbound in the local context
notInFcCtxM :: (PrettyPrint a, MonadReader ctx m, MonadError String m) => (ctx -> a -> Maybe t) -> a -> m ()
notInFcCtxM f x = ask >>= \ctx -> case f ctx x of
  Just {} -> throwErrorM (text "notInFcCtxM" <+> colon <+> ppr x <+> text "is already bound")
  Nothing -> return ()

-- | Ensure the type variable is not already bound
tyVarNotInFcCtxM :: FcTyVar -> FcM ()
tyVarNotInFcCtxM = notInFcCtxM lookupTyVarCtx

-- | Ensure type variables not already bound
tyVarsNotInFcCtxM :: [FcTyVar] -> FcM ()
tyVarsNotInFcCtxM = mapM_ tyVarNotInFcCtxM

-- | Ensure the term variable is not already bound
tmVarNotInFcCtxM :: FcTmVar -> FcM ()
tmVarNotInFcCtxM = notInFcCtxM lookupTmVarCtx

-- | Ensure the list of term variables is not already bound
tmVarsNotInFcCtxM :: [FcTmVar] -> FcM ()
tmVarsNotInFcCtxM = mapM_ tmVarNotInFcCtxM

-- * Type checking
-- ----------------------------------------------------------------------------

-- -- | Type check a top-level value binding
-- tcFcValBind :: FcValBind -> FcM FcCtx
-- tcFcValBind (FcValBind x ty tm) = do
--   tmVarNotInFcCtxM x  -- GEORGE: Ensure is not already bound
--   kind <- tcType ty
--   unless (kind == KStar) $
--     throwError "tcFcValBind: Kind mismatch (FcValBind)"
--   ty' <- extendCtxTmM x ty (tcTerm tm)
--   unless (ty `eqFcTypes` ty') $ throwErrorM (text "Global let type doesnt match:"
--                                 $$ parens (text "given:" <+> ppr ty)
--                                 $$ parens (text "inferred:" <+> ppr ty'))
--   extendCtxTmM x ty ask -- GEORGE: Return the extended environment

-- -- | Type check a program
-- tcFcProgram :: FcProgram -> FcM FcType
-- -- Type check a datatype declaration
-- tcFcProgram (FcPgmDataDecl datadecl pgm) = do
--   tcFcDataDecl datadecl
--   tcFcProgram pgm
-- -- Type check a top-level value binding
-- tcFcProgram (FcPgmValDecl valbind pgm) = do
--   fc_ctx <- tcFcValBind valbind
--   setCtxM fc_ctx $ tcFcProgram pgm
-- -- Type check the top-level program expression
-- tcFcProgram (FcPgmTerm tm) = tcTerm tm

-- -- | Type check a System F term
-- tcTerm :: FcTerm -> FcM FcType
-- tcTerm (FcTmAbs x ty1 tm) = do
--   kind <- tcType ty1 -- GEORGE: Should have kind star
--   unless (kind == KStar) $
--     throwError "tcTerm: Kind mismatch (FcTmAbs)"
--   ty2  <- extendCtxTmM x ty1 (tcTerm tm)
--   return (mkFcArrowTy ty1 ty2)
-- tcTerm (FcTmVar x) = lookupTmVarM x
-- tcTerm (FcTmPrim tm) = tcTmPrim tm
-- tcTerm (FcTmApp tm1 tm2)  = do
--   ty1 <- tcTerm tm1
--   ty2 <- tcTerm tm2
--   case isFcArrowTy ty1 of
--     Just (ty1a, ty1b) -> alphaEqFcTypes ty1a ty2 >>= \case
--       True  -> return ty1b
--       False -> throwErrorM (text "tcTerm" <+> text "FcTmApp" $$ pprPar ty1 $$ pprPar ty2)
--     Nothing           -> throwErrorM (text "Wrong function FcType application"
--                                       $$ parens (text "ty1=" <+> ppr ty1)
--                                       $$ parens (text "ty2=" <+> ppr ty2))

-- tcTerm (FcTmTyAbs a tm) = do
--   tyVarNotInFcCtxM a -- GEORGE: Ensure not already bound
--   ty <- extendCtxTyM a (kindOf a) (tcTerm tm)
--   return (FcTyAbs a ty)
-- tcTerm (FcTmTyApp tm ty) = do
--   kind <- tcType ty
--   tcTerm tm >>= \case
--     FcTyAbs a tm_ty
--       | kindOf a == kind -> return $ substVar a ty tm_ty
--     _other               -> throwError "Malformed type application"

-- tcTerm (FcTmDataCon dc) = mkDataConTy <$> lookupDataConTyM dc
-- tcTerm (FcTmLet x ty tm1 tm2) = do
--   tmVarNotInFcCtxM x -- GEORGE: Ensure not already bound
--   kind <- tcType ty
--   unless (kind == KStar) $
--     throwError "tcTerm: Kind mismatch (FcTmLet)"
--   ty1  <- extendCtxTmM x ty (tcTerm tm1)
--   unless (ty `eqFcTypes` ty1) $ throwError "Let type doesnt match"
--   extendCtxTmM x ty (tcTerm tm2)
-- tcTerm (FcTmCase scr alts) = do
--   scr_ty <- tcTerm scr
--   tcAlts scr_ty alts

-- -- | Type check a list of case alternatives
-- tcAlts :: FcType -> [FcAlt] -> FcM FcType
-- tcAlts scr_ty alts
--   | null alts = throwError "Case alternatives are empty"
--   | otherwise = do
--       rhs_tys <- mapM (tcAlt scr_ty) alts
--       ensureIdenticalTypes rhs_tys
--       let (ty:_) = rhs_tys
--       return ty

-- tcAlt :: FcType -> FcAlt -> FcM FcType
-- tcAlt scr_ty (FcAlt (FcConPat dc xs) rhs) = case tyConAppMaybe scr_ty of
--   Just (tc, tys) -> do
--     tmVarsNotInFcCtxM xs -- GEORGE: Ensure not bound already
--     (as, arg_tys, dc_tc) <- lookupDataConTyM dc
--     unless (dc_tc == tc) $
--       throwErrorM (text "tcAlt" <+> colon <+> text "The type of the scrutinee does not match that of the pattern")
--     let ty_subst     = mconcat (zipWithExact (|->) as tys)
--     let real_arg_tys = map (substFcTyInTy ty_subst) arg_tys
--     extendCtxTmsM xs real_arg_tys (tcTerm rhs)
--   Nothing -> throwErrorM (text "destructScrTy" <+> colon <+> text "Not a tycon application")

-- | Kind check a type
tcType :: FcType -> FcM Kind
tcType (FcTyVar a) = lookupTyVarM a
tcType (FcTyAbs a ty) = do
  tyVarNotInFcCtxM a            -- GEORGE: Ensure not already bound
  k <- extendCtxTyM a (kindOf a) (tcType ty)
  case k of
    KStar  -> return KStar
    _other -> throwError "tcType: Kind mismatch (FcTyAbs)"
tcType (FcTyApp ty1 ty2) = do
  k1 <- tcType ty1
  k2 <- tcType ty2
  case k1 of
    KArr k1a k1b | k1a == k2 -> return k1b
    _otherwise               -> throwError "tcType: Kind mismatch (FcTyApp)"
tcType (FcTyCon tc) = lookupTyConKindM tc

mkDataConTy :: ([FcTyVar], [FcType], FcTyCon) -> FcType
mkDataConTy (as, arg_tys, tc) = fcTyAbs as $ fcTyArr arg_tys $ fcTyConApp tc (map FcTyVar as)

mkPrimOpTy :: ([FcType], FcType) -> FcType
mkPrimOpTy = uncurry fcTyArr


-- | Type check application of types to an operator type
tcFcTyApp :: FcType -> [FcType] -> FcM FcType
tcFcTyApp rt_ty []             = return rt_ty
tcFcTyApp rt_ty (rd_ty:rd_tys) = do
  kind <- tcType rd_ty
  case rt_ty of 
    FcTyAbs a rt_ty'
      | kindOf a == kind -> tcFcTyApp (substVar a rd_ty rt_ty') rd_tys
    _other               -> throwErrorM (text "tcFcTyApp" <+> colon <+> text "malformed type application"
                                         $$ text "type given: " <+> ppr rt_ty <+> text "does not have kind star")


-- | Ensure that all types are syntactically the same
ensureIdenticalTypes :: [FcType] -> FcM ()
ensureIdenticalTypes types = unless (go types) $ throwError "Type mismatch in case rhs"
  where
    go :: [FcType] -> Bool
    go []       = True
    go (ty:tys) = all (eqFcTypes ty) tys

-- | Matches rand_tys to arg_tys with alpha-equality. 
-- |   returns the tail of arg_tys in case rand_tys is shorter than arg_tys
-- |   throws an error when unequal types are encountered, or rand_tys is longer than arg_tys
matchArgumentTypes :: [FcType] -> [FcType] -> FcM [FcType]
matchArgumentTypes rand_tys arg_tys = go rand_tys arg_tys >>= \case
  Just rest_tys -> return rest_tys
  Nothing       -> throwErrorM (text "tcFcOptTmApp" <+> colon <+> text "data constructor argument type mismatch"
        $$ (text "given: " <+> ppr rand_tys)
        $$ (text "expected: " <+> ppr arg_tys))
  where 
    go :: [FcType] -> [FcType] -> FcM (Maybe [FcType])
    go []           []           = return $ Just []
    go []           a_tys        = return $ Just a_tys
    go _            []           = return Nothing
    go (r_ty:r_tys) (a_ty:a_tys) = r_ty `alphaEqFcTypes` a_ty >>= \case
      True  -> go r_tys a_tys
      False -> return Nothing

-- | Yields argument types and result type of a primitive operation
lookupPrimOp :: PrimOp -> FcM ([FcType],FcType)
lookupPrimOp (PrimIntOp _) = return ([mkFcIntTy, mkFcIntTy], mkFcIntTy)

-- | Yields type of a primitive literal
lookupPrimLit :: PrimLit -> FcM FcType
lookupPrimLit (PInt _) = return mkFcIntTy

-- * Phase agnostic type checking functions
-- ----------------------------------------------------------------------------

-- | Type check a data declaration
tcFcDataDecl :: FcDataDecl -> FcM ()
tcFcDataDecl (FcDataDecl _tc as dcs) = do
  forM_ as tyVarNotInFcCtxM  -- GEORGE: Ensure is not already bound
  forM_ dcs $ \(_dc, tys) -> do
    kinds <- extendCtxTysM as (map kindOf as) (mapM tcType tys)
    unless (all (==KStar) kinds) $
      throwError "tcFcDataDecl: Kind mismatch (FcDataDecl)"

-- * Optimizer syntax type checking
-- ----------------------------------------------------------------------------

-- | Typecheck an optimizer program
tcFcOptProgram :: FcOptProgram -> FcM (FcType, FcResProgram)
-- ^ type check a datatype declaration
tcFcOptProgram (FcPgmDataDecl decl pgm) = do
  tcFcDataDecl decl
  (ty, pgm') <- tcFcOptProgram pgm
  return (ty, FcPgmDataDecl decl pgm')
-- ^ type check top level binding and add to context, TC rest of program in new context
tcFcOptProgram (FcPgmValDecl bind pgm) = do
  (ctx, bind') <- tcFcOptBind bind
  (ty, pgm') <- setCtxM ctx $ tcFcOptProgram pgm
  return (ty, FcPgmValDecl bind' pgm')
-- ^ type check program term, wrap into FcPgmTerm
tcFcOptProgram (FcPgmTerm tm) = second FcPgmTerm <$> tcFcOptTerm tm

-- | Type check an optimizer term
tcFcOptTerm :: FcOptTerm -> FcM (FcType, FcResTerm)
-- ^ Type check a term application
tcFcOptTerm (FcOptTmApp t ts) = tcFcOptTmApp t ts
-- ^ Type check a type abstraction
tcFcOptTerm (FcOptTmTyAbs as tm) = tcFcOptTmTyAbs as tm
-- ^ Type check a type application
tcFcOptTerm (FcOptTmTyApp tm tys) = tcFcOptTmTyApp tm tys
-- ^ Type check a case statement
tcFcOptTerm (FcOptTmCase tm alts) = do
  (scr_ty, tm_r) <- tcFcOptTerm tm
  second (FcResTmCase tm_r) <$> tcFcOptAlts scr_ty alts
-- ^ Type check a local let binding
tcFcOptTerm (FcOptTmLet bind t) = do
  (ctx, bind_r) <- tcFcOptBind bind
  second (FcResTmLet [bind_r]) <$> setCtxM ctx (tcFcOptTerm t)
-- ^ Type check a primitive literal
tcFcOptTerm (FcOptTmPrim (PrimLitTm lit)) = lookupPrimLit lit >>= \ty -> return (ty, FcResTmLit lit)
-- ^ Type check a primitive operator (fallback for primop without application around it)
tcFcOptTerm (FcOptTmPrim (PrimOpTm op)) = tcFcOptTmApp (FcOptTmPrim (PrimOpTm op)) []
-- ^ Type check an abstraction (fallback)
tcFcOptTerm (FcOptTmAbs vs tm) = do
  bind <- mkFcResBind (FcOptTmAbs vs tm)
  return (fval_bind_ty bind, FcResTmLet [bind] (FcResTmApp (FcRatorVar $ fval_bind_var bind) []))
-- ^ Type check a term variable (fallback)
tcFcOptTerm (FcOptTmVar x) = lookupTmVarM x >>= \ty -> return (ty, FcResTmApp (FcRatorVar x) [])
-- ^ Type check a datacon (fallback for dc arity 0)
tcFcOptTerm (FcOptTmDataCon dc) = tcFcOptTmApp (FcOptTmDataCon dc) []

-- | Type check a type abstraction
tcFcOptTmTyAbs :: [FcTyVar] -> FcOptTerm -> FcM (FcType, FcResTerm)
tcFcOptTmTyAbs as tm = do
  tyVarsNotInFcCtxM as
  -- bind variables and typecheck term, wrap resulting type into TyABs
  first (fcTyAbs as) <$> extendCtxTysM as (map kindOf as) (tcFcOptTerm tm)

-- | Type check a type application
tcFcOptTmTyApp :: FcOptTerm -> [FcType] -> FcM (FcType, FcResTerm)
tcFcOptTmTyApp tm tys = do
  -- bind term to variable
  bind <- mkFcResBind tm
  res_ty <- tcFcTyApp (fval_bind_ty bind) tys
  let tyapp_r = FcResTmApp (FcRatorVar (fval_bind_var bind)) (map FcAtType tys)
  return (res_ty, FcResTmLet [bind] tyapp_r)

-- | Type check case alts
tcFcOptAlts :: FcType -> FcOptAlts -> FcM (FcType, FcResAlts)
tcFcOptAlts scr_ty alts = do 
  (tys, alts_r) <- case alts of
    (FcAAlts alts') -> second FcAAlts . unzip <$> mapM (tcFcOptAAlt scr_ty) alts'
    (FcPAlts alts') -> second FcPAlts . unzip <$> mapM (tcFcOptPAlt scr_ty) alts'
  ensureIdenticalTypes tys
  return (head tys, alts_r)

-- | Type check a value binding.
tcFcOptBind :: FcOptBind -> FcM (FcCtx, FcResBind)
tcFcOptBind (FcBind x ty tm) = do
  tmVarNotInFcCtxM x  -- GEORGE: Ensure is not already bound
  kind <- tcType ty
  unless (kind == KStar) $
    throwError "tcFcValBind: Kind mismatch (FcValBind)"
  (ty', ab) <- case tm of     -- Type check bound term and put it into FcResAbs
    (FcOptTmAbs vs tm') -> do
      let (xs, tys) = unzip vs
      (ty_tm, tm_r) <- extendCtxTmsM (x:xs) (ty:tys) (tcFcOptTerm tm')
      let ty_ab = foldr mkFcArrowTy ty_tm tys
      return (ty_ab, FcResAbs vs tm_r)
    tm'                 -> do
      (ty_tm, tm_r) <- extendCtxTmM x ty (tcFcOptTerm tm')
      return (ty_tm, FcResAbs [] tm_r)
  unless (ty `eqFcTypes` ty') $ throwErrorM (text "Global let type doesnt match:"
                                $$ parens (text "given:" <+> ppr ty)
                                $$ parens (text "inferred:" <+> ppr ty'))
  ctx_ext <- extendCtxTmM x ty ask -- extend context with bound variable
  return (ctx_ext, FcBind x ty ab)

-- | Type check applicaton of a list of terms to a term
tcFcOptTmApp :: FcOptTerm -> [FcOptTerm] -> FcM (FcType, FcResTerm)
-- ^ application of terms to a variable
tcFcOptTmApp (FcOptTmVar x) tms = do
  rator_ty <- lookupTmVarM x
  (rand_tys, binds, ats) <- tcFcOptTmAppTerms tms
  app_ty <- getAppResultTy rator_ty rand_tys
  return (app_ty, mkFcApp binds (FcRatorVar x) ats)
-- ^ application of terms to a primitive operator (saturated)
tcFcOptTmApp (FcOptTmPrim (PrimOpTm op)) ts = do
  (arg_tys, res_ty) <- lookupPrimOp op
  (rand_tys, binds, ats) <- tcFcOptTmAppTerms ts
  (eta_res_ty, eta_binds, res_tm) <- matchArgumentTypes rand_tys arg_tys >>= \case
    -- application is saturated: nothing to do
    [] -> return (res_ty, binds, FcResTmApp (FcRatorPOp op) ats)
    -- unsaturated: eta expand
    eta_tys -> do
      eta_vars <- mapM (const freshFcTmVar) eta_tys
      -- build eta expanded application, bind to new variable and return
      rator_var <- freshFcTmVar
      let rator_ty = foldr mkFcArrowTy res_ty eta_tys
      let rator_ab = FcResAbs (zipExact eta_vars eta_tys) 
                       (FcResTmApp (FcRatorPOp op) (ats ++ map FcAtVar eta_vars))
      -- add binding, replace application by empty application to variable
      return (rator_ty, FcBind rator_var rator_ty rator_ab:binds, FcResTmApp (FcRatorVar rator_var) [])
  return (eta_res_ty, FcResTmLet eta_binds res_tm)
-- ^ application of terms to data constructor (without type application)
tcFcOptTmApp (FcOptTmDataCon dc) tms = tcFcOptTmApp (FcOptTmTyApp (FcOptTmDataCon dc) []) tms
-- ^ application of terms to data constructor (saturated)
tcFcOptTmApp (FcOptTmTyApp (FcOptTmDataCon dc) k_tys) tms = do
  (as, arg_tys, dc_tc) <- lookupDataConTyM dc              -- Get type of datacon
  let ty_subst = mconcat (zipWithExact (|->) as k_tys)     
  let real_arg_tys = map (substFcTyInTy ty_subst) arg_tys  -- Fully instantiate argument types
  (rand_tys, binds, ats) <- tcFcOptTmAppTerms tms          -- Get type of arguments
  (eta_res_ty, eta_binds, res_tm) <- matchArgumentTypes rand_tys real_arg_tys >>= \case
    -- application is saturated: nothing to do
    [] -> return (fcTyConApp dc_tc k_tys, 
            binds, 
            FcResTmApp (FcRatorCon dc) (map FcAtType k_tys ++ ats))
    -- unsaturated application: eta expand
    eta_tys -> do
      eta_vars <- mapM (const freshFcTmVar) eta_tys
      -- build eta expanded application, bind to new variable and return
      rator_var <- freshFcTmVar
      let rator_ty = foldr mkFcArrowTy (fcTyConApp dc_tc k_tys) eta_tys
      let rator_ab = FcResAbs (zipExact eta_vars eta_tys) 
                       (FcResTmApp (FcRatorCon dc) (map FcAtType k_tys ++ ats ++ map FcAtVar eta_vars))
      -- add binding, replace application by empty application to variable
      return (rator_ty, FcBind rator_var rator_ty rator_ab:binds, FcResTmApp (FcRatorVar rator_var) [])
  return (eta_res_ty, FcResTmLet eta_binds res_tm)
-- ^ application of terms to a term (general case excluding all above)
tcFcOptTmApp t ts = do
  rator_bind <- mkFcResBind t
  (rand_tys, binds, ats) <- tcFcOptTmAppTerms ts
  app_ty <- getAppResultTy (fval_bind_ty rator_bind) rand_tys
  return (app_ty, mkFcApp (rator_bind:binds) (FcRatorVar (fval_bind_var rator_bind)) ats)

tcFcOptAAlt :: FcType -> FcOptAAlt -> FcM (FcType, FcResAAlt)
tcFcOptAAlt scr_ty (FcAAlt (FcConPat dc xs) rhs) = case tyConAppMaybe scr_ty of
  Just (tc, tys) -> do
    tmVarsNotInFcCtxM xs    -- ensure variables not bound in current context
    (as, arg_tys, dc_tc) <- lookupDataConTyM dc
    unless (dc_tc == tc) $
      throwErrorM (text "tcOptAAlt" <+> colon <+> text "The type of the scrutinee does not match that of the pattern")
    let ty_subst = mconcat (zipWithExact (|->) as tys)   -- Create substitution
    let real_arg_tys = map (substFcTyInTy ty_subst) arg_tys  -- and fill in type variables in argument types
    second (FcAAlt (FcConPat dc xs)) <$> extendCtxTmsM xs real_arg_tys (tcFcOptTerm rhs)
  Nothing -> throwErrorM (text "destructScrTy" <+> colon <+> text "Not a tycon application")

tcFcOptPAlt :: FcType -> FcOptPAlt -> FcM (FcType, FcResPAlt)
tcFcOptPAlt scr_ty (FcPAlt lit rhs) = do
  lit_ty <- lookupPrimLit lit
  unless (scr_ty `eqFcTypes` lit_ty) $
    throwErrorM (text "tcOptPAlt" <+> colon <+> text "The type of the scrutinee does not match that of the literal")
  second (FcPAlt lit) <$> tcFcOptTerm rhs


-- | Determine the resulting type from the application
getAppResultTy :: FcType -> [FcType] -> FcM FcType
getAppResultTy rator_ty []                 = return rator_ty
getAppResultTy rator_ty (rand_ty:rand_tys) = case isFcArrowTy rator_ty of
  Just (arg_ty, rator_ty') 
    | arg_ty `eqFcTypes` rand_ty -> getAppResultTy rator_ty' rand_tys
    | otherwise                  -> throwErrorM (text "tcFcOptTmApp" <+> colon <+> text "application types don't match"
    $$ text "given: " <+> ppr rand_ty
    $$ text "inferred: " <+> ppr arg_ty)
  _other -> throwErrorM (text "tcFcOptTmApp" <+> colon <+> text "oversaturated application")


-- | Implementation of the |-app relation
tcFcOptTmAppTerms :: [FcOptTerm] -> FcM ([FcType], [FcResBind], [FcAtom])
tcFcOptTmAppTerms [] = return ([],[],[])
tcFcOptTmAppTerms (t:ts) = do
  (tys, binds, ats) <- tcFcOptTmAppTerms ts
  case t of
    -- variables and literals can directly be added to the atoms list
    (FcOptTmVar x) -> lookupTmVarM x >>= 
      \ty -> return (ty:tys, binds, FcAtVar x  :ats)
    (FcOptTmPrim (PrimLitTm lit)) -> lookupPrimLit lit >>= 
      \ty -> return (ty:tys, binds, FcAtLit lit:ats)
    -- general terms get bound to a variable in the binds list
    _ -> do
      bind <- mkFcResBind t
      return (fval_bind_ty bind:tys, bind:binds, FcAtVar (fval_bind_var bind):ats)
 

mkFcApp :: [FcResBind] -> FcRator -> [FcAtom] -> FcResTerm
mkFcApp []    r ats = FcResTmApp r ats
mkFcApp binds r ats = FcResTmLet binds (FcResTmApp r ats)

-- | Type check a term and produce a binding to a fresh variable
mkFcResBind :: FcOptTerm -> FcM FcResBind
-- ^ Absorb bindings into let if there are any
mkFcResBind (FcOptTmAbs vs tm) = do
  let (xs,tys) = unzip vs
  (ty, tm_r) <- extendCtxTmsM xs tys (tcFcOptTerm tm)
  x <- freshFcTmVar
  return $ FcBind x (foldr mkFcArrowTy ty tys) (FcResAbs vs tm_r)
-- ^ In the other case instantiate empty abstraction
mkFcResBind tm = do
  (ty, tm_r) <- tcFcOptTerm tm
  x <- freshFcTmVar
  return $ FcBind x ty (FcResAbs [] tm_r)

-- * Restricted syntax type checking
-- ----------------------------------------------------------------------------

tcFcResProgram :: FcResProgram -> FcM (FcType, SProg)
tcFcResProgram (FcPgmDataDecl decl pgm) = tcFcDataDecl decl >> tcFcResProgram pgm
tcFcResProgram (FcPgmValDecl  bind pgm) = do
  (new_ctx, binds_s) <- tcFcResBind [bind]                    -- type check binding and get new ctx
  (ty,SProg binds_p) <- setCtxM new_ctx $ tcFcResProgram pgm  -- type check program in new ctx
  return (ty, SProg (binds_s ++ binds_p))                     -- combine bindings into new program
tcFcResProgram (FcPgmTerm tm) = do
  (ty, expr) <- tcFcResTerm tm
  let main_bind = SBind mkStgMainBindVar (SLForm [] NUble [] expr)
  return (ty, SProg [main_bind])
  
-- | Type check a term
tcFcResTerm :: FcResTerm -> FcM (FcType, SExpr)
tcFcResTerm (FcResTmCase tm alts) = do
  (scr_ty, scr_exp) <- tcFcResTerm tm
  second (SCase scr_exp) <$> tcFcResAlts scr_ty alts
tcFcResTerm (FcResTmApp rator ats) = tcFcResApp rator ats
tcFcResTerm (FcResTmTyAbs as tm) = tcFcResTmTyAbs as tm
tcFcResTerm (FcResTmLet binds ab) = throwUnimplErrorM

-- | Type check an application term
tcFcResApp :: FcRator -> [FcAtom] -> FcM (FcType, SExpr)
tcFcResApp (FcRatorVar x) ats = do
  ty_rt <- lookupTmVarM x
  (ty_res, ats_s) <- tcFcResAts ats ty_rt
  let x_s = rnFcTmVarToSVar x
  return (ty_res, SApp x_s ats_s)
tcFcResApp (FcRatorPOp op) ats = do
  ty_op <- mkPrimOpTy <$> lookupPrimOp op
  (ty_res, ats_s) <- tcFcResAts ats ty_op
  return (ty_res, SPApp op ats_s)
tcFcResApp (FcRatorCon dc) ats = do
  ty_dc <- mkDataConTy <$> lookupDataConTyM dc
  (ty_res, ats_s) <- tcFcResAts ats ty_dc
  let dc_s = (SCon . unFcDC) dc
  return (ty_res, SCApp dc_s ats_s)

-- | Type check a type abstraction term
tcFcResTmTyAbs :: [FcTyVar] -> FcResTerm -> FcM (FcType, SExpr)
tcFcResTmTyAbs as tm = do
  tyVarsNotInFcCtxM as
  -- Type check term and wrap type in TyAbs
  first (fcTyAbs as) <$> extendCtxTysM as (map kindOf as) (tcFcResTerm tm)

tcFcResAlts :: FcType -> FcResAlts -> FcM (FcType, SAlts)
tcFcResAlts scr_ty alts = do
  (tys, alts_s) <- case alts of
    (FcAAlts alts') -> second SAAlts . unzip <$> mapM (tcFcResAAlt scr_ty) alts'
    (FcPAlts alts') -> second SPAlts . unzip <$> mapM (tcFcResPAlt scr_ty) alts'
  ensureIdenticalTypes tys
  return (head tys, alts_s)

tcFcResAAlt :: FcType -> FcResAAlt -> FcM (FcType, SAAlt)
tcFcResAAlt _ _ = throwUnimplErrorM
-- tcFcResAAlt scr_ty (FcAAlt (FcConPat dc xs) rhs) = case tyConAppMaybe scr_ty of
--   Just (tc, tys) -> do
--     tmVarsNotInFcCtxM xs    -- ensure variables not bound in current context
--     (as, arg_tys, dc_tc) <- lookupDataConTyM dc
--     unless (dc_tc == tc) $
--       throwErrorM (text "tcOptAAlt" <+> colon <+> text "The type of the scrutinee does not match that of the pattern")
--     let ty_subst = mconcat (zipWithExact (|->) as tys)   -- Create substitution
--     let real_arg_tys = map (substFcTyInTy ty_subst) arg_tys  -- and fill in type variables in argument types
--     second (FcAAlt (FcConPat dc xs)) <$> extendCtxTmsM xs real_arg_tys (tcFcOptTerm rhs)
--   Nothing -> throwErrorM (text "destructScrTy" <+> colon <+> text "Not a tycon application")

tcFcResPAlt :: FcType -> FcResPAlt -> FcM (FcType, SPAlt)
tcFcResPAlt scr_ty (FcPAlt lit rhs) = do
  lit_ty <- lookupPrimLit lit
  unless (scr_ty `eqFcTypes` lit_ty) $
    throwErrorM (text "tcResPAlt" <+> colon <+> text "The type of the scrutinee does not match that of the literal")
  second (SPAlt lit) <$> tcFcResTerm rhs

tcFcResBind :: FcResBind -> FcM (FcCtx,SBind)
tcFcResBind _ = throwUnimplErrorM

-- | Implementation of the |-AT relation
-- | Type checks application of atoms to an operator of type ty_rt
tcFcResAts :: [FcAtom] -> FcType -> FcM (FcType, [SAtom])
tcFcResAts []                ty_rt = return (ty_rt, [])
-- ^ apply a type to the operand type
tcFcResAts (FcAtType ty:ats) ty_rt = case ty_rt of
  (FcTyAbs a ty_rt') -> tcFcResAts ats (substFcTyInTy (a |-> ty) ty_rt')
  _other             -> throwErrorM (text "tcFcResAts" <+> colon <+> text "malformed type application"
                        $$ text "expected TyAbs, got: " <+> ppr ty_rt)
-- ^ apply an operand to the operator
tcFcResAts (rand:ats) ty_rt = do
  -- get operand type and translation
  (ty_rd, at_s) <- case rand of
    (FcAtVar x) -> lookupTmVarM x  >>= \ty -> return (ty, SAtVar $ rnFcTmVarToSVar x)
    (FcAtLit k) -> lookupPrimLit k >>= \ty -> return (ty, SAtLit k)
  -- get result type
  (ty_arg, ty_rt') <- case isFcArrowTy ty_rt of
    Just tys -> return tys
    Nothing -> throwErrorM (text "tcFcResAts" <+> colon <+> text "oversaturated application"
                           $$ text "operator type is: " <+> ppr ty_rt)
  -- check operand type match
  ty_rd `alphaEqFcTypes` ty_arg >>= \eq -> unless eq $
    throwErrorM (text "tcFcResAts" <+> colon <+> text "incorrect argument type"
                $$ text "given:" <+> ppr ty_rd 
                $$ text "expected:" <+> ppr ty_arg)
  second (at_s:) <$> tcFcResAts ats ty_rt'

-- * Invoke the complete System F type checker
-- ----------------------------------------------------------------------------

-- GEORGE: Refine the type and also print more stuff out

-- fcTypeCheck :: (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo) -> UniqueSupply -> FcProgram
--             -> (Either String ((FcType, UniqueSupply), FcGblEnv), Trace)
-- fcTypeCheck (tc_env, dc_env) us pgm = runWriter
--                                     $ runExceptT
--                                     $ flip runStateT  fc_init_gbl_env
--                                     $ flip runReaderT fc_init_ctx
--                                     $ flip runUniqueSupplyT us
--                                     $ tcFcProgram pgm
--   where
--     fc_init_ctx     = mempty
--     fc_init_gbl_env = FcGblEnv tc_env dc_env

-- | Type check an optimizer program and translate it into a restricted program
fcOptElaborate :: FcGblEnv -> UniqueSupply -> FcOptProgram
         -> (Either String (((FcType, FcResProgram), UniqueSupply), FcGblEnv), Trace)
fcOptElaborate fc_init_gbl_env us pgm = runWriter
                                 $ runExceptT
                                 $ flip runStateT  fc_init_gbl_env
                                 $ flip runReaderT fc_init_ctx
                                 $ flip runUniqueSupplyT us
                                 $ tcFcOptProgram pgm
  where
    fc_init_ctx = mempty

-- | Type check a restricted program and translate it into an STG program 
fcResElaborate :: FcGblEnv -> UniqueSupply -> FcResProgram
         -> (Either String (((FcType, SProg), UniqueSupply), FcGblEnv), Trace)
fcResElaborate fc_init_gbl_env us pgm = runWriter
                                 $ runExceptT
                                 $ flip runStateT  fc_init_gbl_env
                                 $ flip runReaderT fc_init_ctx
                                 $ flip runUniqueSupplyT us
                                 $ tcFcResProgram pgm
  where
    fc_init_ctx = mempty