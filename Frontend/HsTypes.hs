{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Frontend.HsTypes where

import Backend.FcTypes

import Utils.Var
import Utils.Kind
import Utils.Annotated
import Utils.Unique
import Utils.FreeVars
import Utils.SnocList
import Utils.PrettyPrint

import Data.List (nub, (\\))

-- * Type Constructors
-- ------------------------------------------------------------------------------

newtype HsTyCon a = HsTC { unHsTC :: a }
  deriving (Eq, Ord)

instance Uniquable a => Uniquable (HsTyCon a) where
  getUnique = getUnique . unHsTC

instance Symable a => Symable (HsTyCon a) where
  symOf = symOf . unHsTC

instance Named a => Named (HsTyCon a) where
  nameOf = nameOf . unHsTC

type PsTyCon = HsTyCon Sym
type RnTyCon = HsTyCon Name

data HsTyConInfo
  = HsTCInfo { hs_tc_ty_con    :: RnTyCon     -- ^ The type constructor name
             , hs_tc_type_args :: [RnTyVar]   -- ^ Universal types
             , hs_tc_fc_ty_con :: FcTyCon }   -- ^ Elaborated Type Constructor

-- * Data Constructors
-- ------------------------------------------------------------------------------

newtype HsDataCon a = HsDC { unHsDC :: a }
  deriving (Eq, Ord)

instance Uniquable a => Uniquable (HsDataCon a) where
  getUnique = getUnique . unHsDC

instance Symable a => Symable (HsDataCon a) where
  symOf = symOf . unHsDC

instance Named a => Named (HsDataCon a) where
  nameOf = nameOf . unHsDC

type PsDataCon = HsDataCon Sym
type RnDataCon = HsDataCon Name

data HsDataConInfo
  -- Normal DataCon
  = HsDCInfo { hs_dc_data_con    :: RnDataCon    -- ^ The data constructor name
             , hs_dc_univ        :: [RnTyVar]    -- ^ Universal type variables
             , hs_dc_parent      :: RnTyCon      -- ^ Parent type constructor
             , hs_dc_arg_tys     :: [RnPolyTy]   -- ^ Argument types
             , hs_dc_fc_data_con :: FcDataCon }  -- ^ Elaborated Data Constructor
  -- DataCon generated for a class
  | HsDCClsInfo { hs_dc_data_con    :: RnDataCon    -- ^ The data constructor name
                , hs_dc_univ        :: [RnTyVar]    -- ^ Universal type variables
                , hs_dc_parent      :: RnTyCon      -- ^ Parent type constructor
                , hs_dc_super       :: RnClsCs
                , hs_dc_arg_tys     :: [RnPolyTy]   -- ^ Argument types
                , hs_dc_fc_data_con :: FcDataCon }  -- ^ Elaborated Data Constructor

-- * Class Names
-- ------------------------------------------------------------------------------

newtype Class a = Class { unClass :: a }
  deriving (Eq, Ord)

instance Uniquable a => Uniquable (Class a) where
  getUnique = getUnique . unClass

instance Symable a => Symable (Class a) where
  symOf = symOf . unClass

instance Named a => Named (Class a) where
  nameOf = nameOf . unClass

type PsClass = Class Sym
type RnClass = Class Name

data ClassInfo
  = ClassInfo { cls_super     :: RnClsCs   -- ^ The superclass constraints
              , cls_class     :: RnClass   -- ^ The class name
              , cls_type_args :: [RnTyVar] -- ^ Type arguments
              , cls_method    :: RnTmVar   -- ^ Method name
              , cls_method_ty :: RnPolyTy  -- ^ Method type
              , cls_tycon     :: RnTyCon   -- ^ Elaborated Type Constructor
              , cls_datacon   :: RnDataCon -- ^ Elaborated Data Constructor
              }

data RnClsInfo
  = RnClsInfo { rn_cls_class     :: RnClass   -- ^ The class name
              , rn_cls_method    :: RnTmVar   -- ^ Method name
              }

-- * Terms
-- ------------------------------------------------------------------------------

data Term a = TmVar (HsTmVar a)                   -- ^ Term variable
            | TmCon (HsDataCon a)                 -- ^ Data constructor
            | TmAbs (HsTmVar a) (Term a)          -- ^ Lambda x . Term
            | TmApp (Term a) (Term a)             -- ^ Term application
            | TmLet (HsTmVar a) (Term a) (Term a) -- ^ Letrec var = term in term
            | TmCase (Term a) [HsAlt a]           -- ^ case e of { ... }

-- | Parsed/renamed term
type PsTerm = Term Sym
type RnTerm = Term Name

data HsAlt a = HsAlt (HsPat a) (Term a)

type PsAlt = HsAlt Sym
type RnAlt = HsAlt Name

data HsPat a = HsPat (HsDataCon a) [HsTmVar a]

type PsPat = HsPat Sym
type RnPat = HsPat Name

instance (Symable a, PrettyPrint a) => PrettyPrint (HsAlt a) where
  ppr (HsAlt pat tm) = ppr pat <+> arrow <+> ppr tm
  needsParens _      = True

instance (Symable a, PrettyPrint a) => PrettyPrint (HsPat a) where
  ppr (HsPat dc xs) = ppr dc <+> hsep (map ppr xs)
  needsParens _     = True

-- * Type Patterns
-- ------------------------------------------------------------------------------

-- | Type Pattern
data HsTyPat a = HsTyConPat (HsTyCon a)             -- ^ Type Constructor pattern
               | HsTyAppPat (HsTyPat a) (HsTyPat a) -- ^ Type Application pattern
               | HsTyVarPat (HsTyVarWithKind a)     -- ^ Type Variable pattern

-- | Parsed/renamed monotype
type PsTyPat = HsTyPat Sym
type RnTyPat = HsTyPat Name

type HsTyVarWithKind a = Ann (HsTyVar a) Kind

type PsTyVarWithKind = HsTyVarWithKind Sym
type RnTyVarWithKind = HsTyVarWithKind Name

-- | Cast a type pattern to a monotype (drop kind annotations)
hsTyPatToMonoTy :: HsTyPat a -> MonoTy a
hsTyPatToMonoTy (HsTyConPat tc)           = TyCon tc
hsTyPatToMonoTy (HsTyAppPat pat1 pat2)    = TyApp (hsTyPatToMonoTy pat1) (hsTyPatToMonoTy pat2)
hsTyPatToMonoTy (HsTyVarPat (a :| _kind)) = TyVar a

-- * Types and Constraints
-- ------------------------------------------------------------------------------

-- | Monotype
data MonoTy a = TyCon (HsTyCon a)           -- ^ Type Constructor
              | TyApp (MonoTy a) (MonoTy a) -- ^ Type Application
              | TyVar (HsTyVar a)           -- ^ Type variable

-- | Parsed/renamed monotype
type PsMonoTy = MonoTy Sym
type RnMonoTy = MonoTy Name

-- | Qualified Type
data QualTy a = QMono (MonoTy a)
              | QQual (ClsCt a) (QualTy a)

-- | Parsed/renamed qualified type
type PsQualTy = QualTy Sym
type RnQualTy = QualTy Name

-- | Polytype
data PolyTy a = PQual (QualTy a)
              | PPoly (HsTyVarWithKind a) (PolyTy a)

-- | Parsed/renamed polytype
type PsPolyTy = PolyTy Sym
type RnPolyTy = PolyTy Name

arrowTyConSym :: Sym
arrowTyConSym = mkSym "(->)"

arrowTyConName :: Name
arrowTyConName = mkName arrowTyConSym arrowTyConUnique

mkPsArrowTy :: PsMonoTy -> PsMonoTy -> PsMonoTy
mkPsArrowTy ty1 ty2 = TyApp (TyApp (TyCon psArrowTyCon) ty1) ty2

psArrowTyCon :: PsTyCon
psArrowTyCon = HsTC arrowTyConSym

rnArrowTyCon :: RnTyCon
rnArrowTyCon = HsTC arrowTyConName

arrowTyConInfo :: HsTyConInfo
arrowTyConInfo = HsTCInfo rnArrowTyCon
                          [ mkRnTyVar (mkName (mkSym "a") arrowTyVar1Unique) KStar
                          , mkRnTyVar (mkName (mkSym "b") arrowTyVar2Unique) KStar ]
                          fcArrowTyCon

-- GEORGE: Needed for pretty printing
isArrowTyCon :: Symable a => HsTyCon a -> Bool
isArrowTyCon (HsTC a) = symOf a == arrowTyConSym

-- isArrowTyCon :: Uniquable a => HsTyCon a -> Bool
-- isArrowTyCon tc = getUnique tc == arrowTyConUnique

-- GEORGE: Needed for pretty printing
isHsArrowTy :: Symable a => MonoTy a -> Maybe (MonoTy a, MonoTy a)
isHsArrowTy (TyApp (TyApp (TyCon tc) ty1) ty2)
  | isArrowTyCon tc   = Just (ty1, ty2)
isHsArrowTy _other_ty = Nothing

-- * Smart constructors
-- ------------------------------------------------------------------------------

-- | Create a type constructor application
mkTyConApp :: HsTyCon a -> [MonoTy a] -> MonoTy a
mkTyConApp tc tys = foldl TyApp (TyCon tc) tys

-- | Make a renamed arrow type (uncurried)
mkRnArrowTy :: [RnMonoTy] -> RnMonoTy -> RnMonoTy
mkRnArrowTy arg_tys res_ty = foldr arr res_ty arg_tys
  where
    arr ty1 ty2 = TyApp (TyApp (TyCon rnArrowTyCon) ty1) ty2

-- * Conversions between monotypes, qualified types and polytypes
-- ------------------------------------------------------------------------------

-- | Convert (is possible) a type scheme into a monotype
polyTyToMonoTy :: PolyTy a -> Maybe (MonoTy a)
polyTyToMonoTy (PQual ty) = qualTyToMonoTy ty
polyTyToMonoTy (PPoly {}) = Nothing

-- | Convert (is possible) a qualified type into a monotype
qualTyToMonoTy :: QualTy a -> Maybe (MonoTy a)
qualTyToMonoTy (QMono ty) = Just ty
qualTyToMonoTy (QQual {}) = Nothing

-- | Lift a monotype to a qualified type
monoTyToQualTy :: MonoTy a -> QualTy a
monoTyToQualTy = QMono

-- | Lift a qualified type to a polytype
qualTyToPolyTy :: QualTy a -> PolyTy a
qualTyToPolyTy = PQual

-- | Lift a monotype to a polytype
monoTyToPolyTy :: MonoTy a -> PolyTy a
monoTyToPolyTy = PQual . QMono

-- | Take a polytype apart
destructPolyTy :: PolyTy a -> ([HsTyVarWithKind a], ClsCs a, MonoTy a) -- GEORGE: Type synonym for lists of type variables?
destructPolyTy (PQual   ty) = ([]  , cs, ty') where     (cs, ty') = destructQualTy ty
destructPolyTy (PPoly a ty) = (a:as, cs, ty') where (as, cs, ty') = destructPolyTy ty

-- | Take a qualified type apart
destructQualTy :: QualTy a -> (ClsCs a, MonoTy a)
destructQualTy (QMono    ty) = ([], ty)
destructQualTy (QQual ct ty) = (ct:cs, ty')
  where (cs, ty') = destructQualTy ty

-- | Inverse of destructPolyTy: create a polytype from parts
constructPolyTy :: ([HsTyVarWithKind a], ClsCs a, MonoTy a) -> PolyTy a
constructPolyTy (as, cs, ty) = foldr PPoly (PQual (constructQualTy (cs,ty))) as

-- | Inverse of destructQualTy: create a qualified type from parts
constructQualTy :: (ClsCs a, MonoTy a) -> QualTy a
constructQualTy (cs, ty) = foldr QQual (QMono ty) cs

-- * Constraints
-- ------------------------------------------------------------------------------

-- | Constraint(s)
data Ctr a   = Ctr [HsTyVarWithKind a] (ClsCs a) (ClsCt a)
type Cts a   = [Ctr a]

-- | Parsed constraint(s)
type PsCtr   = Ctr Sym
type PsCts   = Cts Sym

-- | Renamed constraint(s)
type RnCtr   = Ctr Name
type RnCts   = Cts Name

-- | Class constraint(s)
data ClsCt a = ClsCt (Class a) (MonoTy a)
type ClsCs a = [ClsCt a]

-- | Parsed class constraints(s)
type PsClsCt = ClsCt Sym
type PsClsCs = ClsCs Sym

-- | Renamed class constraint(s)
type RnClsCt = ClsCt Name
type RnClsCs = ClsCs Name

-- | Construct a constraint from a list of type variables, constraints and a class constraint
constructCtr :: ([HsTyVarWithKind a], ClsCs a, ClsCt a) -> Ctr a
constructCtr (as, cs, ty) = Ctr as cs ty

-- * Programs and Declarations
-- ------------------------------------------------------------------------------

-- | Program
data Program a = PgmExp  (Term a)                 -- ^ Expression
               | PgmCls  (ClsDecl  a) (Program a) -- ^ Class declaration
               | PgmInst (InsDecl  a) (Program a) -- ^ Instance declaration
               | PgmData (DataDecl a) (Program a) -- ^ Datatype declaration

-- | Class declaration
data ClsDecl a = ClsD { csuper :: ClsCs a           -- ^ Superclass constraints
                      , cname  :: Class a           -- ^ Class name
                      , cvar   :: HsTyVarWithKind a -- ^ Type variable
                      , cmena  :: HsTmVar a         -- ^ Method name
                      , cmety  :: PolyTy a }        -- ^ Method type

-- | Instance declaration
data InsDecl a = InsD { icons :: ClsCs a        -- ^ Constraints
                      , iname :: Class a        -- ^ Class name
                      , ivar  :: HsTyPat a      -- ^ Instance type
                      , imena :: HsTmVar a      -- ^ Method name
                      , imetm :: Term a }       -- ^ Method term

-- | Datatype Declaration
data DataDecl a = DataD { dtycon    :: HsTyCon a                     -- ^ Type constructor
                        , dtyvars   :: [HsTyVarWithKind a]           -- ^ Universal type variables
                        , ddatacons :: [(HsDataCon a, [MonoTy a])] } -- ^ Data constructors

-- | Parsed/renamed programs
type PsProgram = Program Sym
type RnProgram = Program Name

-- | Parsed/renamed class declarations
type PsClsDecl = ClsDecl Sym
type RnClsDecl = ClsDecl Name

-- | Parsed/renamed instance declarations
type PsInsDecl = InsDecl Sym
type RnInsDecl = InsDecl Name

-- | Parsed/renamed datatype declarations
type PsDataDecl = DataDecl Sym
type RnDataDecl = DataDecl Name

-- * Additional Syntax For Type Inference And Elaboration
-- ------------------------------------------------------------------------------

-- | All constraints (equality and class)
type Cs = (EqCs, RnClsCs)

-- | Equality constraint(s)
data EqCt = RnMonoTy :~: RnMonoTy
type EqCs = [EqCt]

-- | Variable-annotated constraints
type AnnCtr = Ann DictVar RnCtr
type AnnCts = SnocList AnnCtr

-- | Variable-annotated class constraints
type AnnClsCt = Ann DictVar RnClsCt
type AnnClsCs = SnocList AnnClsCt

-- | The program theory is just a list of name-annotated constrains
type ProgramTheory       = AnnCts
type SimpleProgramTheory = SnocList AnnClsCt

progTheoryFromSimple :: SimpleProgramTheory -> ProgramTheory
progTheoryFromSimple = fmap (\(d :| c) -> d :| constructCtr ([],[],c))

data FullTheory = FT { theory_super :: ProgramTheory
                     , theory_inst  :: ProgramTheory
                     , theory_local :: ProgramTheory }

-- | Extend the superclass component of the theory
ftExtendSuper :: FullTheory -> ProgramTheory -> FullTheory
ftExtendSuper theory super_cs = theory { theory_super = theory_super theory `mappend` super_cs }

-- | Extend the instance component of the theory
ftExtendInst :: FullTheory -> ProgramTheory -> FullTheory
ftExtendInst theory inst_cs = theory { theory_inst = theory_inst theory `mappend` inst_cs }

-- | Extend the local component of the theory
ftExtendLocal :: FullTheory -> ProgramTheory -> FullTheory
ftExtendLocal theory local_cs = theory { theory_local = theory_local theory `mappend` local_cs }

-- | Collapse the full program theory to a program theory (just concatenate)
ftToProgramTheory :: FullTheory -> ProgramTheory
ftToProgramTheory (FT super inst local) = mconcat [super,inst,local]

-- | Drop the superclass component of the full theory and turn it into a program theory (concatenate)
ftDropSuper :: FullTheory -> ProgramTheory
ftDropSuper (FT _super inst local) = inst `mappend` local

-- * Collecting Free Variables Out Of Objects
-- ------------------------------------------------------------------------------

instance ContainsFreeTyVars (Ann DictVar RnCtr) RnTyVar where
  ftyvsOf (_ :| ct) = ftyvsOf ct

-- GEORGE: Careful. This does not check that the kinds are the same for every
-- occurence of a type variable.
instance Eq a => ContainsFreeTyVars (HsTyPat a) (HsTyVarWithKind a) where
  ftyvsOf = nub . ftyvsOfTyPat
    where
      -- | Free variables of a type pattern (with multiplicities)
      ftyvsOfTyPat :: HsTyPat a -> [HsTyVarWithKind a]
      ftyvsOfTyPat (HsTyConPat {})      = []
      ftyvsOfTyPat (HsTyAppPat ty1 ty2) = ftyvsOfTyPat ty1 ++ ftyvsOfTyPat ty2
      ftyvsOfTyPat (HsTyVarPat v)       = [v]

instance Eq a => ContainsFreeTyVars (MonoTy a) (HsTyVar a) where
  ftyvsOf = nub . ftyvsOfMonoTy
    where
      -- | Free variables of a monotype (with multiplicities)
      ftyvsOfMonoTy :: MonoTy a -> [HsTyVar a]
      ftyvsOfMonoTy (TyCon {})      = []
      ftyvsOfMonoTy (TyApp ty1 ty2) = ftyvsOfMonoTy ty1 ++ ftyvsOfMonoTy ty2
      ftyvsOfMonoTy (TyVar v)       = [v]

instance Eq a => ContainsFreeTyVars (Ctr a) (HsTyVar a) where
  ftyvsOf (Ctr [] [] ct)        = ftyvsOf ct
  ftyvsOf (Ctr [] (ct1:cs) ct2) = nub (ftyvsOf ct1 ++ ftyvsOf (Ctr [] cs ct2))
  ftyvsOf (Ctr (a:as) cs ct)    = ftyvsOf (Ctr as cs ct) \\ [labelOf a]

instance Eq a => ContainsFreeTyVars (ClsCt a) (HsTyVar a) where
  ftyvsOf (ClsCt _ ty) = ftyvsOf ty

instance ContainsFreeTyVars EqCt RnTyVar where
  ftyvsOf (ty1 :~: ty2) = nub (ftyvsOf ty1 ++ ftyvsOf ty2)

instance Eq a => ContainsFreeTyVars (QualTy a) (HsTyVar a) where
  ftyvsOf (QMono ty)    = ftyvsOf ty
  ftyvsOf (QQual ct ty) = nub (ftyvsOf ct ++ ftyvsOf ty)

instance Eq a => ContainsFreeTyVars (PolyTy a) (HsTyVar a) where
  ftyvsOf (PQual ty)   = ftyvsOf ty
  ftyvsOf (PPoly a ty) = ftyvsOf ty \\ [labelOf a]

-- * Pretty Printing
-- ------------------------------------------------------------------------------

-- | Pretty print a type constructor
instance Symable a => PrettyPrint (HsTyCon a) where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print type constructor info
instance PrettyPrint HsTyConInfo where
  ppr (HsTCInfo _tc type_args _fc_ty_con)
    = braces $ vcat $ punctuate comma
    $ [
        text "univ" <+> colon <+> ppr (map (\ty -> ty :| kindOf ty) type_args)
      ]
  needsParens _ = False

-- | Pretty print a data constructor
instance Symable a => PrettyPrint (HsDataCon a) where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print data constructor info
instance PrettyPrint HsDataConInfo where
  ppr (HsDCInfo _dc univs tc arg_tys _dc_fc_data_con)
    = braces $ hsep $ punctuate comma
    $ [
        text "univ"    <+> colon <+> ppr univs
      , text "parent"  <+> colon <+> ppr tc
      , text "arg_tys" <+> colon <+> ppr arg_tys
      ]
  ppr (HsDCClsInfo _dc univs tc super arg_tys _dc_fc_data_con)
    = braces $ hsep $ punctuate comma
    $ [
        text "univ"    <+> colon <+> ppr univs
      , text "parent"  <+> colon <+> ppr tc
      , text "super"   <+> colon <+> ppr super
      , text "arg_tys" <+> colon <+> ppr arg_tys
      ]
  needsParens _ = False

-- | Pretty print class names
instance Symable a => PrettyPrint (Class a) where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print type class info
instance PrettyPrint ClassInfo where
  ppr (ClassInfo cs cls type_args method method_ty tycon datacon)
    = braces $ vcat $ punctuate comma
    $ [ text "cls_super"     <+> colon <+> ppr cs
      , text "cls_class"     <+> colon <+> ppr cls
      , text "cls_type_args" <+> colon <+> ppr type_args
      , text "cls_method"    <+> colon <+> ppr method
      , text "cls_method_ty" <+> colon <+> ppr method_ty
      , text "cls_tycon"     <+> colon <+> ppr tycon
      , text "cls_datacon"   <+> colon <+> ppr datacon
      ]
  needsParens _ = False

instance PrettyPrint FullTheory where
  ppr (FT super inst local)
    = braces $ vcat $ punctuate comma
    $ [ text "theory_super" <+> colon <+> ppr super
      , text "theory_inst"  <+> colon <+> ppr inst
      , text "theory_local" <+> colon <+> ppr local
      ]
  needsParens _ = False

-- | Pretty print renamer's type class info
instance PrettyPrint RnClsInfo where
  ppr (RnClsInfo cls method)
    = braces $ vcat $ punctuate comma
    $ [ text "cls_class"     <+> colon <+> ppr cls
      , text "cls_method"    <+> colon <+> ppr method
      ]
  needsParens _ = False

-- | Pretty print terms
instance (Symable a, PrettyPrint a) => PrettyPrint (Term a) where
  ppr (TmVar v)          = ppr v
  ppr (TmCon dc)         = ppr dc
  ppr (TmAbs v tm)       = backslash <> ppr v <> dot <+> ppr tm
  ppr (TmApp tm1 tm2)
    | TmApp {} <- tm1    = ppr tm1    <+> pprPar tm2
    | otherwise          = pprPar tm1 <+> pprPar tm2
  ppr (TmLet v tm1 tm2)  = colorDoc yellow (text "let") <+> ppr v <+> equals <+> ppr tm1
                        $$ colorDoc yellow (text "in")  <+> ppr tm2
  ppr (TmCase scr alts)  = hang (text "case" <+> ppr scr <+> text "of") 2 (vcat $ map ppr alts)

  needsParens (TmAbs  {}) = True
  needsParens (TmApp  {}) = True
  needsParens (TmLet  {}) = True
  needsParens (TmCase {}) = True
  needsParens (TmVar  {}) = False
  needsParens (TmCon  {}) = False

-- | Pretty print type patterns
instance (Symable a, PrettyPrint a) => PrettyPrint (HsTyPat a) where
  ppr = ppr . hsTyPatToMonoTy

  needsParens (HsTyConPat {}) = False
  needsParens (HsTyAppPat {}) = True
  needsParens (HsTyVarPat {}) = False

-- | Pretty print monotypes
instance (Symable a, PrettyPrint a) => PrettyPrint (MonoTy a) where
  ppr ty | Just (ty1, ty2) <- isHsArrowTy ty
         = case isHsArrowTy ty1 of
             Just {} -> pprPar ty1 <+> arrow <+> ppr ty2
             Nothing -> ppr ty1    <+> arrow <+> ppr ty2
  ppr (TyCon tc)      = ppr tc
  ppr (TyApp ty1 ty2)
    | TyApp {} <- ty1 = ppr ty1    <+> pprPar ty2
    | otherwise       = pprPar ty1 <+> pprPar ty2
  ppr (TyVar var)     = ppr var

  needsParens (TyCon {}) = False
  needsParens (TyApp {}) = True
  needsParens (TyVar {}) = False

-- | Pretty print qualified types
instance (Symable a, PrettyPrint a) => PrettyPrint (QualTy a) where
  ppr (QMono    ty) = ppr ty
  ppr (QQual ct ty)
    | let dct = pprPar ct
    = dct <+> darrow <+> ppr ty

  needsParens (QMono ty) = needsParens ty
  needsParens (QQual {}) = True

-- | Pretty print polytypes
instance (Symable a, PrettyPrint a) => PrettyPrint (PolyTy a) where
  ppr (PQual   ty) = ppr ty
  ppr (PPoly a ty) = text "forall" <+> ppr a <> dot <+> ppr ty

  needsParens (PQual ty) = needsParens ty
  needsParens (PPoly {}) = True

-- | Pretty print constraints
instance (Symable a, PrettyPrint a) => PrettyPrint (Ctr a) where
  ppr (Ctr [] [] ct)        = ppr ct
  ppr (Ctr [] (ct1:cs) ct2) = (ppr ct1) <+> darrow <+> (ppr (Ctr [] cs ct2))
  ppr (Ctr (a:as) cs ct)    = text "forall" <+> ppr a <> dot <+> ppr (Ctr as cs ct)

  needsParens _ = True

isClsCtr :: Ctr a -> Bool
isClsCtr (Ctr [] [] _) = True
isClsCtr _other        = False

isImplCtr :: Ctr a -> Bool
isImplCtr (Ctr [] [] _) = False
isImplCtr (Ctr [] _ _)  = True
isImplCtr _other        = False

isAbsCtr :: Ctr a -> Bool
isAbsCtr (Ctr [] _ _) = False
isAbsCtr _other       = True

-- | Pretty print class constraints
instance (Symable a, PrettyPrint a) => PrettyPrint (ClsCt a) where
  ppr (ClsCt cls ty) = ppr cls <+> pprPar ty
  needsParens _      = True

-- | Pretty print programs
instance (Symable a, PrettyPrint a) => PrettyPrint (Program a) where
  ppr (PgmExp tm)         = ppr tm
  ppr (PgmCls  cdecl pgm) = ppr cdecl $$ ppr pgm
  ppr (PgmInst idecl pgm) = ppr idecl $$ ppr pgm
  ppr (PgmData ddecl pgm) = ppr ddecl $$ ppr pgm

  needsParens _ = False

-- | Pretty print class declarations
instance (Symable a, PrettyPrint a) => PrettyPrint (ClsDecl a) where
  ppr (ClsD cs cName cVar mName mTy)
    = hang (colorDoc green (text "class") <+> pprCs cs <+> darrow <+> ppr cName <+> pprPar cVar <+> colorDoc green (text "where"))
           2
           (ppr (symOf mName) <+> dcolon <+> ppr mTy)
    where
      pprCs = parens . sep . punctuate comma . map ppr

  needsParens _ = False

-- | Pretty print class instances
instance (Symable a, PrettyPrint a) => PrettyPrint (InsDecl a) where
  ppr (InsD cs cName cTy mName mExp)
    = hang (colorDoc green (text "instance") <+> pprCs cs <+> darrow <+> ppr cName <+> pprPar cTy <+> colorDoc green (text "where"))
           2
           (ppr mName <+> equals <+> ppr mExp)
    where
      pprCs = parens . sep . punctuate comma . map ppr

  needsParens _ = False

-- | Pretty print datatype declarations
instance (Symable a, PrettyPrint a) => PrettyPrint (DataDecl a) where
  ppr (DataD tc as dcs) = hsep [colorDoc green (text "data"), ppr tc, hsep (map ppr as), cons]
    where
      ppr_dc (dc, tys) = hsep (colorDoc yellow (char '|') : ppr dc : map pprPar tys)

      cons = sep $ case dcs of
        []               -> []
        ((dc, tys):rest) -> hsep (colorDoc yellow (char '=') : ppr dc : map pprPar tys) : map ppr_dc rest

  needsParens _ = False

-- | Pretty print equality constraints
instance PrettyPrint EqCt where
  ppr (ty1 :~: ty2) = ppr ty1 <+> text "~" <+> ppr ty2
  needsParens _ = True
