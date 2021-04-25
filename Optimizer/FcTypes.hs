{-|
Module      : Optimizer.FcTypes
Description : System F types used in the optimiser

Datatypes representing the System F AST, with supporting functions and smart constructors.
System F syntax is split into two phases:
- Optimiser phase, marked with the @Opt type. These implement "vanilla" system F as it is most commonly seen.
- Preprocessed phase, marked with the @Pre type. This variant is preprocessed to be as easily translated into STG as possible.
The main differences are:
- Prepped System F only allows lambda bindings inside let
- Prepped System F supports multi variable abstraction and application
-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds             #-}

module Optimizer.FcTypes where

import Utils.AssocList
import Utils.Unique
import Utils.Var
import Utils.Kind
import Utils.Prim
import Utils.PrettyPrint
import Utils.Annotated
import Utils.FreeVars

import Data.Maybe (isJust)
import Data.Function (on)
import Data.List ((\\))

-- * Global typechecking environment
-- ----------------------------------------------------------------------------

data FcGblEnv = FcGblEnv { fc_env_tc_info :: AssocList FcTyCon   FcTyConInfo
                         , fc_env_dc_info :: AssocList FcDataCon FcDataConInfo
                         }

-- * Arrow Type Constructor
-- ----------------------------------------------------------------------------

mkFcArrowTy :: FcType -> FcType -> FcType
mkFcArrowTy ty1 ty2 = FcTyApp (FcTyApp (FcTyCon fcArrowTyCon) ty1) ty2

fcArrowTyCon :: FcTyCon
fcArrowTyCon = FcTC (mkName (mkSym "(->)") arrowTyConUnique)

isFcArrowTy :: FcType -> Maybe (FcType, FcType)
isFcArrowTy (FcTyApp (FcTyApp (FcTyCon tc) ty1) ty2)
  | tc == fcArrowTyCon  = Just (ty1, ty2)
isFcArrowTy _other_type = Nothing

-- * Primitive Type Constructors
-- ----------------------------------------------------------------------------

mkFcIntTy :: FcType
mkFcIntTy = FcTyCon fcIntTyCon

fcIntTyCon :: FcTyCon
fcIntTyCon = FcTC (mkName (mkSym "Int#") intTyConUnique)

isFcPrimLitTy :: FcType -> Maybe ()
isFcPrimLitTy (FcTyCon tc) -- to integrate more primlit types, add more guards
  | tc == fcIntTyCon = Just ()
isFcPrimLitTy _          = Nothing

mkIntBinopTy :: FcType
mkIntBinopTy = mkFcArrowTy mkFcIntTy (mkFcArrowTy mkFcIntTy mkFcIntTy)

-- * Types
-- ----------------------------------------------------------------------------
data FcType = FcTyVar  FcTyVar        -- ^ Type variable
            | FcTyAbs  FcTyVar FcType -- ^ Type abstraction
            | FcTyApp  FcType  FcType -- ^ Type application
            | FcTyCon  FcTyCon        -- ^ Type constructor

-- | Syntactic equality on System F types
eqFcTypes :: FcType -> FcType -> Bool
eqFcTypes (FcTyVar v1)    (FcTyVar v2)    = v1 == v2
eqFcTypes (FcTyAbs v1 t1) (FcTyAbs v2 t2) = (v1 == v2)      && eqFcTypes t1 t2
eqFcTypes (FcTyApp t1 t2) (FcTyApp t3 t4) = eqFcTypes t1 t3 && eqFcTypes t2 t4
eqFcTypes (FcTyCon tc1)   (FcTyCon tc2)   = tc1 == tc2

eqFcTypes (FcTyVar {}) _  = False
eqFcTypes (FcTyAbs {}) _  = False
eqFcTypes (FcTyApp {}) _  = False
eqFcTypes (FcTyCon {}) _  = False

-- | Type Constructors
newtype FcTyCon = FcTC { unFcTC :: Name }

instance Eq FcTyCon where
  (==) = (==) `on` unFcTC

instance Ord FcTyCon where
  compare = compare `on` unFcTC

instance Symable FcTyCon where
  symOf = symOf . unFcTC

instance Named FcTyCon where
  nameOf = unFcTC

instance Uniquable FcTyCon where
  getUnique = getUnique . unFcTC

data FcTyConInfo
  = FcTCInfo { fc_tc_ty_con    :: FcTyCon     -- ^ The type constructor name
             , fc_tc_type_args :: [FcTyVar] } -- ^ Universal types

-- | Pretty print type constructor info
instance PrettyPrint FcTyConInfo where
  ppr (FcTCInfo tc type_args)
    = braces $ vcat $ punctuate comma
    $ [ text "fc_tc_ty_con"    <+> colon <+> ppr tc
      , text "fc_tc_type_args" <+> colon <+> ppr type_args
      ]

  needsParens _ = False

-- | Data Constructors
newtype FcDataCon = FcDC { unFcDC :: Name }
  deriving (Eq, Ord)

instance Symable FcDataCon where
  symOf = symOf . unFcDC

instance Named FcDataCon where
  nameOf = unFcDC

instance Uniquable FcDataCon where
  getUnique = getUnique . unFcDC

data FcDataConInfo
  = FcDCInfo { fc_dc_data_con :: FcDataCon  -- ^ The data constructor name
             , fc_dc_univ     :: [FcTyVar]  -- ^ Universal type variables
             , fc_dc_parent   :: FcTyCon    -- ^ Parent type constructor
             , fc_dc_arg_tys  :: [FcType] } -- ^ Argument types

-- | Pretty print data constructor info
instance PrettyPrint FcDataConInfo where
  ppr (FcDCInfo dc univ tc arg_tys)
    = braces $ vcat $ punctuate comma
    $ [ text "fc_dc_data_con" <+> colon <+> ppr dc
      , text "fc_dc_univ"     <+> colon <+> ppr univ
      , text "fc_dc_parent"   <+> colon <+> ppr tc
      , text "fc_dc_arg_tys"  <+> colon <+> ppr arg_tys
      ]
  needsParens _ = False

-- -- | Take the type apart the hindley milner way
-- destructFcTypeHM :: FcType -> ([FcTyVar], [FcType], FcType)
-- destructFcTypeHM (FcTyArr ty1 ty2) = (as, ty1:lhs, rhs)
--   where (as, lhs, rhs) = destructFcTypeHM ty2
-- destructFcTypeHM (FcTyAbs a ty) = (a:as, lhs, rhs)
--   where (as, lhs, rhs) = destructFcTypeHM ty
-- destructFcTypeHM ty@(FcTyVar  {}) = ([], [], ty)
-- destructFcTypeHM ty@(FcTyApp  {}) = ([], [], ty)
-- destructFcTypeHM ty@(FcTyCon  {}) = ([], [], ty)

constructFcTypeHM :: ([FcTyVar], [FcType], FcType) -> FcType
constructFcTypeHM (as, tys, ty) = fcTyAbs as (fcTyArr tys ty)

-- | Take apart a type constructor application
tyConAppMaybe :: FcType -> Maybe (FcTyCon, [FcType])
tyConAppMaybe ty = go ty []
  where
    go :: FcType -> [FcType] -> Maybe (FcTyCon, [FcType])
    go (FcTyApp ty1 ty2)  tys = go ty1 (ty2:tys)
    go (FcTyCon tc)       tys = Just (tc, tys)
    go _other_ty         _tys = Nothing

-- * Some smart constructors (uncurried variants)
-- ----------------------------------------------------------------------------

-- | Uncurried version of data constructor FcTyAbs
fcTyAbs :: [FcTyVar] -> FcType -> FcType
fcTyAbs vars ty = foldr FcTyAbs ty vars

-- | Uncurried version of data constructor FcTyArr
fcTyArr :: [FcType] -> FcType -> FcType
fcTyArr tys ty = foldr mkFcArrowTy ty tys

-- | Uncurried version of data constructor FcTyApp
fcTyApp :: FcType -> [FcType] -> FcType
fcTyApp ty tys = foldl FcTyApp ty tys

-- | Apply a type constructor to a bunch of types
fcTyConApp :: FcTyCon -> [FcType] -> FcType
fcTyConApp tc tys = fcTyApp (FcTyCon tc) tys

-- * Programs and declarations
-- ----------------------------------------------------------------------------

-- | Data Type Declaration
data FcDataDecl = FcDataDecl { fdata_decl_tc   :: FcTyCon                 -- ^ Type Constructor
                             , fdata_decl_tv   :: [FcTyVar]               -- ^ Universal Type variables
                             , fdata_decl_cons :: [(FcDataCon, [FcType])] -- ^ Data Constructors
                             }

-- | Program, parametrised in the type of term and the type of term bound by a value binding
data FcProgram a b 
  = FcPgmDataDecl FcDataDecl (FcProgram a b) -- ^ Data Declaration
  | FcPgmValDecl  (FcBind b) (FcProgram a b) -- ^ Value Binding
  | FcPgmTerm     a                          -- ^ Term

type FcOptProgram = FcProgram FcOptTerm FcOptTerm
type FcResProgram = FcProgram FcResTerm FcResAbs

-- * Terms
-- ----------------------------------------------------------------------------

-- | Syntax for the optimizer
data FcOptTerm 
  = FcOptTmVar FcTmVar                       -- ^ Variable
  | FcOptTmPrim PrimTm                       -- ^ Primitive
  | FcOptTmDataCon FcDataCon                 -- ^ Data constructor
  | FcOptTmAbs [(FcTmVar,FcType)] FcOptTerm  -- ^ Lambda abstraction
  | FcOptTmApp FcOptTerm [FcOptTerm]         -- ^ Application
  | FcOptTmTyAbs [FcTyVar] FcOptTerm         -- ^ Type abstraction
  | FcOptTmTyApp FcOptTerm [FcType]          -- ^ Type application
  | FcOptTmLet FcOptBind FcOptTerm           -- ^ let bind in term
  | FcOptTmCase FcOptTerm (FcAlts FcOptTerm) -- ^ case term of alts

-- | Syntax preprocessed for translation to STG
data FcResTerm
  = FcResTmApp FcRator [FcAtom]              -- ^ Application on variable, primop or contructor
  | FcResTmTyAbs [FcTyVar] FcResTerm         -- ^ (Multiple) type abstraction
  | FcResTmLet [FcResBind] FcResTerm         -- ^ let bind in term
  | FcResTmCase FcResTerm (FcAlts FcResTerm) -- ^ case term of alts
  | FcResTmLit PrimLit                       -- ^ Primitive literal

-- | Value binding
data FcBind a where
  FcBind :: { fval_bind_var :: FcTmVar
            , fval_bind_ty  :: FcType 
            , fval_bind_tm  :: a 
            } -> FcBind a

type FcOptBind = FcBind FcOptTerm -- ^ Optimizer binds regular terms
type FcResBind = FcBind FcResAbs  -- ^ Preprocessed syntax binds abstractions of terms

-- | Lambda abstraction
data FcResAbs = FcResAbs [(FcTmVar,FcType)] FcResTerm

-- | Operand
data FcRator = FcRatorVar FcTmVar
             | FcRatorPOp PrimOp
             | FcRatorCon FcDataCon

-- | Atom
data FcAtom = FcAtVar FcTmVar 
            | FcAtLit PrimLit 
            | FcAtType FcType

data FcAlts a 
  = FcAAlts [FcAAlt a]              -- ^ Algebraic alternatives
  | FcPAlts [FcPAlt a]              -- ^ Primitive alternatives

type FcOptAlts = FcAlts FcOptTerm
type FcResAlts = FcAlts FcResTerm

-- | Pattern over ADT
data FcAAlt a = FcAAlt FcConPat a

type FcOptAAlt = FcAAlt FcOptTerm
type FcResAAlt = FcAAlt FcResTerm

-- | Pattern with primitive literal
data FcPAlt a = FcPAlt PrimLit a

type FcOptPAlt = FcPAlt FcOptTerm
type FcResPAlt = FcPAlt FcResTerm

-- | Data constructor pattern
data FcConPat = FcConPat FcDataCon [FcTmVar]

-- * Some smart constructors (uncurried variants)
-- ----------------------------------------------------------------------------

-- | Uncurried version of data constructor FcTmAbs
fcOptTmAbs :: [(FcTmVar, FcType)] -> FcOptTerm -> FcOptTerm
fcOptTmAbs = FcOptTmAbs

-- | Uncurried version of data constructor FcTmTyAbs
fcOptTmTyAbs :: [FcTyVar] -> FcOptTerm -> FcOptTerm
fcOptTmTyAbs = FcOptTmTyAbs

-- | Uncurried version of data constructor FcTmApp
fcOptTmApp :: FcOptTerm -> [FcOptTerm] -> FcOptTerm
fcOptTmApp = FcOptTmApp

-- | Uncurried version of data constructor FcTmTyApp
fcOptTmTyApp :: FcOptTerm -> [FcType] -> FcOptTerm
fcOptTmTyApp = FcOptTmTyApp

-- | Create a data constructor application
fcOptDataConApp :: FcDataCon -> FcType -> [FcOptTerm] -> FcOptTerm
fcOptDataConApp dc ty = fcOptTmApp (FcOptTmTyApp (FcOptTmDataCon dc) [ty])

-- | Apply a term to a list of dictionary variables
fcOptDictApp :: FcOptTerm -> [DictVar] -> FcOptTerm
fcOptDictApp tm ds = FcOptTmApp tm (map FcOptTmVar ds)

-- * Collecting Free Type Variables Out Of Objects
-- ------------------------------------------------------------------------------

instance ContainsFreeTyVars FcType FcTyVar where
  ftyvsOf (FcTyVar a)       = [a]
  ftyvsOf (FcTyAbs a ty)    = ftyvsOf ty \\ [a]
  ftyvsOf (FcTyApp ty1 ty2) = ftyvsOf ty1 ++ ftyvsOf ty2
  ftyvsOf (FcTyCon _)      = []

instance ContainsFreeTyVars FcOptTerm FcTyVar where
  ftyvsOf (FcOptTmVar  _)        = []
  ftyvsOf (FcOptTmPrim _)        = []
  ftyvsOf (FcOptTmAbs vs tm)     = (ftyvsOf.snd.unzip) vs ++ ftyvsOf tm
  ftyvsOf (FcOptTmApp tm1 tm2)   = ftyvsOf tm1 ++ ftyvsOf tm2
  ftyvsOf (FcOptTmTyAbs a tm)    = ftyvsOf tm \\ a
  ftyvsOf (FcOptTmTyApp tm ty)   = ftyvsOf tm ++ ftyvsOf ty
  ftyvsOf (FcOptTmDataCon _)     = []
  ftyvsOf (FcOptTmLet bd tm)     = ftyvsOf bd ++ ftyvsOf tm
  ftyvsOf (FcOptTmCase tm alts)  = ftyvsOf tm ++ ftyvsOf alts

instance ContainsFreeTyVars FcResTerm FcTyVar where
  ftyvsOf (FcResTmApp _ ats)    = ftyvsOf ats
  ftyvsOf (FcResTmTyAbs as tm)  = ftyvsOf tm \\ as
  ftyvsOf (FcResTmLet bd tm)    = ftyvsOf bd ++ ftyvsOf tm
  ftyvsOf (FcResTmCase tm alts) = ftyvsOf tm ++ ftyvsOf alts
  ftyvsOf (FcResTmLit _)        = []

instance ContainsFreeTyVars FcOptBind FcTyVar where
  ftyvsOf (FcBind _ a tm) = ftyvsOf a ++ ftyvsOf tm

instance ContainsFreeTyVars FcResBind FcTyVar where
  ftyvsOf (FcBind _ a ab) = ftyvsOf a ++ ftyvsOf ab

instance ContainsFreeTyVars FcResAbs FcTyVar where
  ftyvsOf (FcResAbs vs tm) = (ftyvsOf.snd.unzip) vs ++ ftyvsOf tm

instance ContainsFreeTyVars FcAtom FcTyVar where
  ftyvsOf FcAtVar {} = []
  ftyvsOf FcAtLit {} = []
  ftyvsOf (FcAtType  ty) = ftyvsOf ty

instance ContainsFreeTyVars (FcAlts FcOptTerm) FcTyVar where
  ftyvsOf (FcAAlts alts) = ftyvsOf alts
  ftyvsOf (FcPAlts alts) = ftyvsOf alts

instance ContainsFreeTyVars (FcAlts FcResTerm) FcTyVar where
  ftyvsOf (FcAAlts alts) = ftyvsOf alts
  ftyvsOf (FcPAlts alts) = ftyvsOf alts

instance ContainsFreeTyVars (FcAAlt FcOptTerm) FcTyVar where
  ftyvsOf (FcAAlt _ tm) = ftyvsOf tm

instance ContainsFreeTyVars (FcAAlt FcResTerm) FcTyVar where
  ftyvsOf (FcAAlt _ tm) = ftyvsOf tm

instance ContainsFreeTyVars (FcPAlt FcOptTerm) FcTyVar where
  ftyvsOf (FcPAlt _ tm) = ftyvsOf tm

instance ContainsFreeTyVars (FcPAlt FcResTerm) FcTyVar where
  ftyvsOf (FcPAlt _ tm) = ftyvsOf tm

-- * Collecting Free Term Variables Out Of Terms
-- ------------------------------------------------------------------------------

instance ContainsFreeTmVars FcOptTerm FcTmVar where
  ftmvsOf (FcOptTmVar x)        = [x]
  ftmvsOf (FcOptTmPrim _)       = []
  ftmvsOf (FcOptTmDataCon _)    = []
  ftmvsOf (FcOptTmAbs vs tm)    = ftmvsOf tm \\ (fst . unzip) vs
  ftmvsOf (FcOptTmApp tm tms)   = ftmvsOf tm ++ ftmvsOf tms
  ftmvsOf (FcOptTmTyAbs _ tm)   = ftmvsOf tm
  ftmvsOf (FcOptTmTyApp tm _)   = ftmvsOf tm
  ftmvsOf (FcOptTmLet bind tm)  = (ftmvsOf bind ++ ftmvsOf tm) \\ [fval_bind_var bind]
  ftmvsOf (FcOptTmCase tm alts) = ftmvsOf tm ++ ftmvsOf alts

instance ContainsFreeTmVars FcResTerm FcTmVar where
  ftmvsOf (FcResTmApp rt ats)   = ftmvsOf rt ++ ftmvsOf ats
  ftmvsOf (FcResTmTyAbs _ tm)   = ftmvsOf tm
  ftmvsOf (FcResTmLet binds tm) = (ftmvsOf binds ++ ftmvsOf tm) \\ map fval_bind_var binds
  ftmvsOf (FcResTmCase tm alts) = ftmvsOf tm ++ ftmvsOf alts
  ftmvsOf (FcResTmLit _)        = []

instance ContainsFreeTmVars a FcTmVar => ContainsFreeTmVars (FcBind a) FcTmVar where
  ftmvsOf (FcBind x _ rhs) = ftmvsOf rhs \\ [x]

instance ContainsFreeTmVars FcResAbs FcTmVar where
  ftmvsOf (FcResAbs vs tm) = ftmvsOf tm \\ (fst . unzip) vs

instance ContainsFreeTmVars FcRator FcTmVar where
  ftmvsOf (FcRatorVar x) = [x]
  ftmvsOf _other         = []

instance ContainsFreeTmVars FcAtom FcTmVar where
  ftmvsOf (FcAtVar x) = [x]
  ftmvsOf _other      = []

instance ContainsFreeTmVars a FcTmVar => ContainsFreeTmVars (FcAlts a) FcTmVar where
  ftmvsOf (FcAAlts alts) = ftmvsOf alts
  ftmvsOf (FcPAlts alts) = ftmvsOf alts

instance ContainsFreeTmVars a FcTmVar => ContainsFreeTmVars (FcAAlt a) FcTmVar where
  ftmvsOf (FcAAlt (FcConPat _ xs) tm) = ftmvsOf tm \\ xs

instance ContainsFreeTmVars a FcTmVar => ContainsFreeTmVars (FcPAlt a) FcTmVar where
  ftmvsOf (FcPAlt _ tm) = ftmvsOf tm

-- * Pretty printing
-- ----------------------------------------------------------------------------

instance PrettyPrint FcGblEnv where
  ppr (FcGblEnv tc_infos dc_infos)
    = braces $ vcat $ punctuate comma
    [ text "fc_env_tc_info" <+> colon <+> ppr tc_infos
    , text "fc_env_dc_info" <+> colon <+> ppr dc_infos ]
  needsParens _ = False

isFcTyApp :: FcType -> Bool
isFcTyApp FcTyApp {} = True
isFcTyApp _other       = False

isFcTyAbs :: FcType -> Bool
isFcTyAbs FcTyAbs {} = True
isFcTyAbs _other       = False

-- | Pretty print types
instance PrettyPrint FcType where
  ppr ty | Just (ty1, ty2) <- isFcArrowTy ty
         , let d1 = if isJust (isFcArrowTy ty1) || isFcTyAbs ty1
                      then pprPar ty1
                      else ppr ty1
         , let d2 = if isJust (isFcArrowTy ty2) || isFcTyApp ty2
                      then ppr ty2
                      else pprPar ty2
         = d1 <+> arrow <+> d2

  ppr (FcTyVar a)       = ppr a
  ppr (FcTyAbs a ty)    = text "forall" <+> ppr a <> dot <+> ppr ty
  ppr (FcTyApp ty1 ty2)
    | FcTyApp {} <- ty1 = ppr ty1    <+> pprPar ty2
    | otherwise         = pprPar ty1 <+> pprPar ty2
  ppr (FcTyCon tc)      = ppr tc

  needsParens FcTyApp {} = True
  needsParens FcTyAbs {} = True
  needsParens FcTyVar {} = False
  needsParens FcTyCon {} = False

-- | Pretty print type constructors
instance PrettyPrint FcTyCon where
  ppr           = ppr . symOf -- Do not show the uniques on the constructors
  needsParens _ = False

-- | Pretty print data constructors
instance PrettyPrint FcDataCon where
  ppr           = ppr . symOf -- Do not show the uniques on the constructors
  needsParens _ = False

-- | Pretty print terms
instance PrettyPrint FcOptTerm where
  ppr (FcOptTmVar x)            = ppr x
  ppr (FcOptTmPrim ptm)         = ppr ptm   
  ppr (FcOptTmAbs vs tm)        = hang 
                                    (backslash <> hsepmap (\ (x, ty) -> parens (ppr x <+> dcolon <+> ppr ty) <> dot) vs) 
                                    2 (ppr tm)
  ppr (FcOptTmApp tm1 tm2)
    | FcOptTmApp   {} <- tm1    = ppr tm1    <+> pprPar tm2
    | FcOptTmTyApp {} <- tm1    = ppr tm1    <+> pprPar tm2
    | otherwise                 = pprPar tm1 <+> pprPar tm2
  ppr (FcOptTmTyAbs tv tm)      = hang (colorDoc yellow (text "/\\") <> ppr tv <> dot) 2 (ppr tm)
  ppr (FcOptTmTyApp tm ty)      = pprPar tm <+> brackets (ppr ty)
  ppr (FcOptTmDataCon dc)       = ppr dc
  ppr (FcOptTmLet bind tm)
    =  (colorDoc yellow (text "let") <+> ppr bind)
    $$ (colorDoc yellow (text "in" ) <+> ppr tm  )
  ppr (FcOptTmCase tm alts)        = hang (colorDoc yellow (text "case") <+> ppr tm <+> colorDoc yellow (text "of"))
                                       2 (ppr alts)

  needsParens FcOptTmVar      {} = False
  needsParens FcOptTmPrim     {} = False
  needsParens FcOptTmAbs      {} = True
  needsParens FcOptTmApp      {} = True
  needsParens FcOptTmTyAbs    {} = True
  needsParens FcOptTmTyApp    {} = True
  needsParens FcOptTmDataCon  {} = False
  needsParens FcOptTmLet      {} = True
  needsParens FcOptTmCase     {} = True

instance PrettyPrint FcResTerm where
  ppr (FcResTmApp rand ats)   = foldl (<+>) (ppr rand) (map pprPar ats)
  ppr (FcResTmTyAbs tvs tm)   = foldr ((<+>) . pprLbd) (ppr tm) tvs
    where pprLbd a = hang (colorDoc yellow (text "/\\") <> ppr a <> dot) 2 (ppr tm)

  ppr (FcResTmLet bind tm)
    =  (colorDoc yellow (text "let") <+> ppr bind)
    $$ (colorDoc yellow (text "in" ) <+> ppr tm  )
  ppr (FcResTmCase tm alts)   = hang (colorDoc yellow (text "case") <+> ppr tm <+> colorDoc yellow (text "of"))
                                  2 (ppr alts)
  ppr (FcResTmLit lit)        = ppr lit 

  needsParens FcResTmApp   {} = True
  needsParens FcResTmTyAbs {} = True
  needsParens FcResTmLet   {} = True
  needsParens FcResTmCase  {} = True
  needsParens FcResTmLit   {} = False

-- | Pretty print variable bindings
instance PrettyPrint FcOptBind where
  ppr (FcBind x ty tm) = ppr x <+> ((colon <+> ppr ty) $$ (equals <+> ppr tm))
  needsParens _ = False

instance PrettyPrint FcResBind where
  ppr (FcBind x ty ab) = ppr x <+> ((colon <+> ppr ty) $$ (equals <+> ppr ab))
  needsParens _ = False

-- | Pretty print lambda abstractions
instance PrettyPrint FcResAbs where
  ppr (FcResAbs vs tm) = hang (backslash <> hsepmap (\ (x, ty) -> parens (ppr x <+> dcolon <+> ppr ty) <> dot) vs) 2 (ppr tm)
  needsParens _ = False

-- | Pretty print operands
instance PrettyPrint FcRator where
  ppr (FcRatorVar x)   = ppr x
  ppr (FcRatorPOp op)  = ppr op
  ppr (FcRatorCon con) = ppr con
  needsParens _       = False

-- | Pretty print atoms
instance PrettyPrint FcAtom where
  ppr (FcAtVar x) = ppr x
  ppr (FcAtLit l) = ppr l
  ppr (FcAtType ty) = ppr ty
  needsParens _ = False

-- | Pretty print alternatives
instance PrettyPrint (FcAlts FcOptTerm) where
  ppr (FcAAlts alts) = vcat $ map ppr alts
  ppr (FcPAlts alts) = vcat $ map ppr alts
  needsParens _      = False 
instance PrettyPrint (FcAlts FcResTerm) where
  ppr (FcAAlts alts) = vcat $ map ppr alts
  ppr (FcPAlts alts) = vcat $ map ppr alts
  needsParens _      = False 

-- | Pretty print algebraic alts
instance PrettyPrint (FcAAlt FcOptTerm) where
  ppr (FcAAlt pat tm) = ppr pat <+> arrow <+> ppr tm
  needsParens _       = True
instance PrettyPrint (FcAAlt FcResTerm) where
  ppr (FcAAlt pat tm) = ppr pat <+> arrow <+> ppr tm
  needsParens _       = True

-- | Pretty print primitive alts
instance PrettyPrint (FcPAlt FcOptTerm) where
  ppr (FcPAlt lit tm) = ppr lit <+> arrow <+> ppr tm
  needsParens _       = True
instance PrettyPrint (FcPAlt FcResTerm) where
  ppr (FcPAlt lit tm) = ppr lit <+> arrow <+> ppr tm
  needsParens _       = True

-- | Pretty print datacon patterns
instance PrettyPrint FcConPat where
  ppr (FcConPat dc xs) = ppr dc <+> hsep (map ppr xs)
  needsParens _     = True

-- | Pretty print data declarations
instance PrettyPrint FcDataDecl where
  ppr (FcDataDecl tc as dcs) = hsep [colorDoc green (text "data"), ppr tc, hsep (map ppr ann_as), cons]
    where
      ann_as = map (\ a -> a :| kindOf a) as
      ppr_dc (dc, tys) = hsep (colorDoc yellow (char '|') : ppr dc : map pprPar tys)

      cons = sep $ case dcs of
        []               -> []
        ((dc, tys):rest) -> hsep (equals : ppr dc : map pprPar tys) : map ppr_dc rest

  needsParens _ = False

-- | Pretty print programs
instance PrettyPrint (FcProgram FcOptTerm FcOptTerm) where
  ppr (FcPgmDataDecl datadecl pgm) = ppr datadecl $$ ppr pgm
  ppr (FcPgmValDecl  valbind  pgm) 
    = colorDoc yellow (text "let") <+> ppr valbind
    $$ ppr pgm
  ppr (FcPgmTerm tm)               = ppr tm
  needsParens _ = False

instance PrettyPrint (FcProgram FcResTerm FcResAbs) where
  ppr (FcPgmDataDecl datadecl pgm) = ppr datadecl $$ ppr pgm
  ppr (FcPgmValDecl  valbind  pgm) 
    = colorDoc yellow (text "let") <+> ppr valbind
    $$ ppr pgm
  ppr (FcPgmTerm tm)               = ppr tm
  needsParens _ = False
