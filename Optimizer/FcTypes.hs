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
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Optimizer.FcTypes where

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

-- | Program
data FcProgram a = FcPgmDataDecl FcDataDecl (FcProgram a)     -- ^ Data Declaration
                 | FcPgmValDecl  (FcBind a) (FcProgram a)     -- ^ Value Binding
                 | FcPgmTerm (FcTerm a)                       -- ^ Term

type FcOptProgram = FcProgram Opt
type FcPreProgram = FcProgram Pre

-- * Terms
-- ----------------------------------------------------------------------------

-- | Optimizer marker type
data Opt
-- | Preprocessed marker type
data Pre

class FcTmMarker a
instance FcTmMarker Opt
instance FcTmMarker Pre

data FcTerm a where
  -- Optimizer language concepts
  -- ^ Variable
  FcOptTmVar :: FcTmVar -> FcOptTerm
  -- ^ Primitive
  FcOptTmPrim :: PrimTm -> FcOptTerm
  -- ^ Lambda abstraction
  FcOptTmAbs :: FcAbs Opt -> FcOptTerm
  -- ^ Application
  FcOptTmApp :: FcOptTerm -> FcOptTerm -> FcOptTerm
  -- ^ Type abstraction
  FcOptTmTyAbs :: FcTyVar -> FcOptTerm -> FcOptTerm
  -- ^ Type application
  FcOptTmTyApp :: FcOptTerm -> FcType -> FcOptTerm
  -- ^ Data constructor
  FcOptTmDataCon :: FcDataCon -> FcOptTerm
  -- Preprocessed language concepts
  -- ^ Application on variable
  FcPreTmVarApp :: FcTmVar   -> [FcAtom] -> FcPreTerm
  -- ^ Application on data constructor (saturated)
  FcPreTmDCApp  :: FcDataCon -> [FcAtom] -> FcPreTerm
  -- ^ Application on primitive operator (saturated)
  FcPreTmPApp   :: PrimOp    -> [FcAtom] -> FcPreTerm
  -- ^ (Multiple) type abstraction
  FcPreTmTyAbs :: [FcTyVar] -> FcPreTerm -> FcPreTerm
  -- Universal concepts
  -- ^ Let binding
  FcTmLet  :: FcBind a -> FcTerm a -> FcTerm a
  -- ^ Case statement
  FcTmCase :: FcTerm a -> FcAlts a -> FcTerm a

type FcOptTerm = FcTerm Opt
type FcPreTerm = FcTerm Pre

-- | Value binding
data FcBind a where 
  -- ^ Optimizer value binding
  FcOptBind :: { fval_bind_opt_var :: FcTmVar
               , fval_bind_opt_ty  :: FcType 
               , fval_bind_opt_tm  :: FcOptTerm 
               } -> (FcBind Opt)
  -- ^ Preprocessed value binding
  FcPreBind :: { fval_bind_pre_var :: FcTmVar
               , fval_bind_pre_ty  :: FcType 
               , fval_bind_pre_abs :: FcAbs Pre 
               } -> (FcBind Pre) 

-- | Lambda abstraction
data FcAbs a where
  FcOptAbs ::  FcTmVar  ->  FcType  -> FcOptTerm -> FcAbs Opt
  FcPreAbs :: [FcTmVar] -> [FcType] -> FcPreTerm -> FcAbs Pre

-- | Atom
data FcAtom = FcAtVar FcTmVar 
            | FcAtLit PrimLit 
            | FcAtType FcType

data FcAlts a = FcAAlts [FcAAlt a]  -- ^ Algebraic alternatives
              | FcPAlts [FcPAlt a]  -- ^ Primitive alternatives

-- | Pattern over ADT
data FcAAlt a = FcAAlt  FcConPat (FcTerm a)
-- | Pattern with primitive literal
data FcPAlt a = FcPAlt  PrimLit  (FcTerm a)

-- | Data constructor pattern
data FcConPat = FcConPat FcDataCon [FcTmVar]

-- * Collecting Free Variables Out Of Objects
-- ------------------------------------------------------------------------------

instance ContainsFreeTyVars FcType FcTyVar where
  ftyvsOf (FcTyVar a)       = [a]
  ftyvsOf (FcTyAbs a ty)    = ftyvsOf ty \\ [a]
  ftyvsOf (FcTyApp ty1 ty2) = ftyvsOf ty1 ++ ftyvsOf ty2
  ftyvsOf (FcTyCon _)      = []

instance (FcTmMarker a) => ContainsFreeTyVars (FcTerm a) FcTyVar where
  -- Opt
  ftyvsOf (FcOptTmVar  _)        = []
  ftyvsOf (FcOptTmPrim _)        = []
  ftyvsOf (FcOptTmAbs ab)        = ftyvsOf ab
  ftyvsOf (FcOptTmApp tm1 tm2)   = ftyvsOf tm1 ++ ftyvsOf tm2
  ftyvsOf (FcOptTmTyAbs a tm)    = ftyvsOf tm \\ [a]
  ftyvsOf (FcOptTmTyApp tm ty)   = ftyvsOf tm ++ ftyvsOf ty
  ftyvsOf (FcOptTmDataCon _)    = []
  -- Pre
  ftyvsOf (FcPreTmVarApp _ ats) = ftyvsOf ats
  ftyvsOf (FcPreTmDCApp  _ ats) = ftyvsOf ats
  ftyvsOf (FcPreTmPApp   _ ats) = ftyvsOf ats
  ftyvsOf (FcPreTmTyAbs as tm)  = ftyvsOf tm \\ as
  -- Universal
  ftyvsOf (FcTmLet bd tm)       = ftyvsOf bd ++ ftyvsOf tm
  ftyvsOf (FcTmCase tm alts)    = ftyvsOf tm ++ ftyvsOf alts

instance (FcTmMarker a) => ContainsFreeTyVars (FcBind a) FcTyVar where
  ftyvsOf (FcOptBind _ a tm) = ftyvsOf a ++ ftyvsOf tm
  ftyvsOf (FcPreBind _ a ab) = ftyvsOf a ++ ftyvsOf ab

instance (FcTmMarker a) => ContainsFreeTyVars (FcAbs a) FcTyVar where
  ftyvsOf (FcOptAbs _ a  tm) = ftyvsOf a  ++ ftyvsOf tm
  ftyvsOf (FcPreAbs _ as tm) = ftyvsOf as ++ ftyvsOf tm

instance ContainsFreeTyVars FcAtom FcTyVar where
  ftyvsOf FcAtVar {} = []
  ftyvsOf FcAtLit {} = []
  ftyvsOf (FcAtType  ty) = ftyvsOf ty

instance (FcTmMarker a) => ContainsFreeTyVars (FcAlts a) FcTyVar where
  ftyvsOf (FcAAlts alts) = ftyvsOf alts
  ftyvsOf (FcPAlts alts) = ftyvsOf alts

instance (FcTmMarker a) => ContainsFreeTyVars (FcAAlt a) FcTyVar where
  ftyvsOf (FcAAlt _ tm) = ftyvsOf tm

instance (FcTmMarker a) => ContainsFreeTyVars (FcPAlt a) FcTyVar where
  ftyvsOf (FcPAlt _ tm) = ftyvsOf tm

-- * Pretty printing
-- ----------------------------------------------------------------------------

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
instance (FcTmMarker a) => PrettyPrint (FcTerm a) where
  ppr (FcOptTmVar x)            = ppr x
  ppr (FcOptTmPrim ptm)         = ppr ptm   
  ppr (FcOptTmAbs b)            = ppr b
  ppr (FcOptTmApp tm1 tm2)
    | FcOptTmApp   {} <- tm1    = ppr tm1    <+> pprPar tm2
    | FcOptTmTyApp {} <- tm1    = ppr tm1    <+> pprPar tm2
    | otherwise                 = pprPar tm1 <+> pprPar tm2
  ppr (FcOptTmTyAbs tv tm)      = hang (colorDoc yellow (text "/\\") <> ppr tv <> dot) 2 (ppr tm)
  ppr (FcOptTmTyApp tm ty)      = pprPar tm <+> brackets (ppr ty)
  ppr (FcOptTmDataCon dc)       = ppr dc
  
  ppr (FcPreTmVarApp var ats)   = foldl (<+>) (ppr var) (map pprPar ats)
  ppr (FcPreTmDCApp  dc  ats)   = foldl (<+>) (ppr dc ) (map pprPar ats)
  ppr (FcPreTmPApp   op  ats)   = foldl (<+>) (ppr op ) (map pprPar ats)
  ppr (FcPreTmTyAbs tvs tm)     = foldr ((<+>) . pprLbd) (ppr tm) tvs
    where pprLbd a = hang (colorDoc yellow (text "/\\") <> ppr a <> dot) 2 (ppr tm)

  ppr (FcTmLet bind tm)
    =  (colorDoc yellow (text "let") <+> ppr bind)
    $$ (colorDoc yellow (text "in" ) <+> ppr tm  )
  ppr (FcTmCase tm alts)        = hang (colorDoc yellow (text "case") <+> ppr tm <+> colorDoc yellow (text "of"))
                                       2 (ppr alts)

  needsParens FcOptTmVar      {} = False
  needsParens FcOptTmPrim     {} = False
  needsParens FcOptTmAbs      {} = True
  needsParens FcOptTmApp      {} = True
  needsParens FcOptTmTyAbs    {} = True
  needsParens FcOptTmTyApp    {} = True
  needsParens FcOptTmDataCon  {} = False
  
  needsParens FcPreTmVarApp   {} = True
  needsParens FcPreTmDCApp    {} = True
  needsParens FcPreTmPApp     {} = True
  needsParens FcPreTmTyAbs    {} = True
  needsParens FcTmLet         {} = True
  needsParens FcTmCase        {} = True

-- | Pretty print variable bindings
instance (FcTmMarker a) => PrettyPrint (FcBind a) where
  ppr (FcOptBind x ty tm) = ppr x <+> ((colon <+> ppr ty) $$ (equals <+> ppr tm))
  ppr (FcPreBind x ty ab) = ppr x <+> ((colon <+> ppr ty) $$ (equals <+> ppr ab))
  needsParens _ = False

-- | Pretty print lambda abstractions
instance (FcTmMarker a) => PrettyPrint (FcAbs a) where
  ppr (FcOptAbs x  ty  tm) = hang (backslash <> parens (ppr x <+> dcolon <+> ppr ty) <> dot) 2 (ppr tm)
  ppr (FcPreAbs xs tys tm) = hang 
                               (backslash
                                 <>
                                   hsepmap
                                     (\ (x, ty) -> parens (ppr x <+> dcolon <+> ppr ty) <> dot)
                                     (zip xs tys)) 
                              2 (ppr tm)
  needsParens _ = False

-- | Pretty print atoms
instance PrettyPrint FcAtom where
  ppr (FcAtVar x) = ppr x
  ppr (FcAtLit l) = ppr l
  ppr (FcAtType ty) = ppr ty
  needsParens _ = False

-- | Pretty print alternatives
instance (FcTmMarker a) => PrettyPrint (FcAlts a) where
  ppr (FcAAlts alts) = vcat $ map ppr alts
  ppr (FcPAlts alts) = vcat $ map ppr alts
  needsParens _      = False 

-- | Pretty print algebraic alts
instance (FcTmMarker a) => PrettyPrint (FcAAlt a) where
  ppr (FcAAlt pat tm) = ppr pat <+> arrow <+> ppr tm
  needsParens _       = True

-- | Pretty print primitive alts
instance (FcTmMarker a) => PrettyPrint (FcPAlt a) where
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
instance (FcTmMarker a) => PrettyPrint (FcProgram a) where
  ppr (FcPgmDataDecl datadecl pgm) = ppr datadecl $$ ppr pgm
  ppr (FcPgmValDecl  valbind  pgm) 
    = colorDoc yellow (text "let") <+> ppr valbind
    $$ ppr pgm
  ppr (FcPgmTerm tm)               = ppr tm
  needsParens _ = False