{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE GADTs             #-}

module Utils.Var
( -- * Parser output: Sym
  Sym, mkSym, Symable(..)
  -- * Renamer output: Name
, Name, mkName, Named(..)
  -- * Source variables
, HsTyVar, HsTmVar, PsTyVar, PsTmVar, RnTyVar, RnTmVar
, mkPsTmVar, mkPsTyVar, mkRnTmVar, mkRnTyVar, rnTyVarToPsTyVar
  -- * Target variables and dictionary variables
, FcTyVar, FcTmVar, DictVar
  -- * Convert a source renamed variable to a target variable of the same kind
, rnTmVarToFcTmVar, rnTyVarToFcTyVar
  -- * Generating fresh variables
, freshRnTmVar, freshRnTyVar, freshFcTmVar, freshFcTyVar, freshDictVar
) where

import Utils.Unique
import Utils.PrettyPrint
import Utils.Kind

import Data.Function (on)

-- * Parser Output: Sym (String Wrapper)
-- ------------------------------------------------------------------------------

newtype Sym = MkSym { unSym :: String }
  deriving (Eq, Ord)

instance Show Sym where
  show = unSym

instance PrettyPrint Sym where
  ppr           = text . unSym
  needsParens _ = False

-- | Create a symbol from a string
mkSym :: String -> Sym
mkSym = MkSym

-- * Renamer Output: Names (Sym + Unique)
-- ------------------------------------------------------------------------------

data Name = MkName { name_name   :: Sym
                   , name_unique :: Unique }

instance Uniquable Name where
    getUnique = name_unique

instance Eq Name where
  (==) = (==) `on` getUnique

instance Ord Name where
  compare = compare `on` getUnique

instance PrettyPrint Name where
  ppr (MkName n u) = ppr n <> underscore <> ppr u
  needsParens _    = False

-- | Create a name from a symbol and a unique
mkName :: Sym -> Unique -> Name
mkName = MkName

-- * Source Variables
-- ------------------------------------------------------------------------------

-- | Source term variables
newtype HsTmVar a = HsTmVar { hstmvar_name :: a }

-- | Source type variables
data HsTyVar :: * -> * where
  PsTyVar :: Sym  ->         HsTyVar Sym
  RnTyVar :: Name -> Kind -> HsTyVar Name
    -- GEORGE: The only reason we store the kind inside is because of the
    -- unification variables that do not get into the environment gamma

instance Eq a => Eq (HsTmVar a) where
  (==) = (==) `on` hstmvar_name

instance Eq a => Eq (HsTyVar a) where
  (PsTyVar a  ) == (PsTyVar b  ) = (a == b)
  (RnTyVar a _) == (RnTyVar b _) = (a == b)
  _ == _ = error "We need >= GHC 8.0 to avoid this.."

-- | Parsed term and type variables
type PsTmVar = HsTmVar Sym
type PsTyVar = HsTyVar Sym

-- | Renamed term and type variables
type RnTmVar = HsTmVar Name
type RnTyVar = HsTyVar Name

-- | Create a parsed term variable
mkPsTmVar :: Sym -> PsTmVar
mkPsTmVar = HsTmVar

-- | Create a parsed type variable
mkPsTyVar :: Sym -> PsTyVar
mkPsTyVar = PsTyVar

-- | Create a renamed term variable
mkRnTmVar :: Name -> RnTmVar
mkRnTmVar = HsTmVar

-- | Create a renamed type variable
mkRnTyVar :: Name -> Kind -> RnTyVar
mkRnTyVar = RnTyVar

-- | Drop information to convert a renamed type variable to a parsed one
rnTyVarToPsTyVar :: RnTyVar -> PsTyVar
rnTyVarToPsTyVar = PsTyVar . symOf

instance PrettyPrint a => PrettyPrint (HsTmVar a) where
  ppr           = ppr . hstmvar_name
  needsParens _ = False

instance PrettyPrint a => PrettyPrint (HsTyVar a) where
  ppr (PsTyVar name  ) = ppr name
  ppr (RnTyVar name _) = ppr name
  needsParens _        = False

instance Uniquable a => Uniquable (HsTmVar a) where
  getUnique = getUnique . hstmvar_name

instance Uniquable a => Uniquable (HsTyVar a) where
  getUnique (PsTyVar name  ) = getUnique name
  getUnique (RnTyVar name _) = getUnique name

-- * Target Variables
-- ------------------------------------------------------------------------------

newtype FcTmVar = FcTmVar { fctmvar_name :: Name }
  deriving (Eq, Ord)

data FcTyVar = FcTyVar { fctyvar_name :: Name
                       , fctyvar_kind :: Kind }

instance Eq FcTyVar where
  (==) = (==) `on` fctyvar_name

instance Ord FcTyVar where
  compare = compare `on` fctyvar_name

instance PrettyPrint FcTmVar where
  ppr           = ppr . fctmvar_name
  needsParens _ = False

instance PrettyPrint FcTyVar where
  ppr           = ppr . fctyvar_name
  needsParens _ = False

-- mkFcTyVar :: Name -> FcTyVar
-- mkFcTyVar = FV
--
-- mkFcTmVar :: Name -> FcTmVar
-- mkFcTmVar = FV

instance Uniquable FcTmVar where
  getUnique = getUnique . fctmvar_name

instance Uniquable FcTyVar where
  getUnique = getUnique . fctyvar_name

-- | Convert a source renamed variable to a System F variable
rnTyVarToFcTyVar :: HsTyVar Name -> FcTyVar
rnTyVarToFcTyVar (RnTyVar name kind) = FcTyVar name kind
rnTyVarToFcTyVar _ {- PsTyVar {} -}  = error "We need GHC 8.0"

-- | Convert a source renamed term variable to a System F type variable
rnTmVarToFcTmVar :: HsTmVar Name -> FcTmVar
rnTmVarToFcTmVar (HsTmVar name) = FcTmVar name

-- * The Symable Class: Everything we can get a Sym out of
-- ------------------------------------------------------------------------------

class Symable a where
  symOf :: a -> Sym

instance Symable Sym where
  symOf = id

instance Symable Name where
  symOf = name_name

instance Symable a => Symable (HsTmVar a) where
  symOf = symOf . hstmvar_name

instance Symable (HsTyVar a) where
  symOf (PsTyVar sym)        = sym
  symOf (RnTyVar name _kind) = symOf name

instance Symable FcTmVar where
  symOf = name_name . fctmvar_name

instance Symable FcTyVar where
  symOf = name_name . fctyvar_name

-- * The Named Class: Everything we can get a Name out of
-- ------------------------------------------------------------------------------

class Symable a => Named a where
  nameOf :: a -> Name

instance Named Name where
  nameOf = id

instance Named (HsTmVar Name) where
  nameOf = hstmvar_name

instance Named (HsTyVar Name) where
  nameOf (RnTyVar name _kind) = name
  nameOf _ {- PsTyVar {} -}   = error "We need GHC 8.0"

instance Named FcTmVar where
  nameOf = fctmvar_name

instance Named FcTyVar where
  nameOf = fctyvar_name

-- * Kinded Instances
-- ------------------------------------------------------------------------------

instance Kinded (HsTyVar Name) where
  kindOf (RnTyVar _name kind) = kind
  kindOf _ {- PsTyVar {} -}   = error "We need GHC 8.0"

instance Kinded FcTyVar where
  kindOf = fctyvar_kind

-- * Dictionary Variables (GEORGE: For Now Just System F Terms. FIXME)
-- ------------------------------------------------------------------------------

-- | Dictionary variables are just System F terms
type DictVar = FcTmVar

-- * Generating Fresh Variables
-- ------------------------------------------------------------------------------

-- | Create a fresh renamed term variable
freshRnTmVar :: MonadUnique m => m RnTmVar
freshRnTmVar = getUniqueM >>= return . HsTmVar . MkName (MkSym "x")

-- | Create a fresh renamed term variable
freshRnTyVar :: MonadUnique m => Kind -> m RnTyVar
freshRnTyVar k = getUniqueM >>= return . flip RnTyVar k . MkName (MkSym "t")

-- | Generate a fresh System F term variable
freshFcTmVar :: MonadUnique m => m FcTmVar
freshFcTmVar = getUniqueM >>= return . FcTmVar . MkName (MkSym "x")

-- | Generate a fresh System F type variable
freshFcTyVar :: MonadUnique m => Kind -> m FcTyVar
freshFcTyVar k = getUniqueM >>= return . flip FcTyVar k . MkName (MkSym "t")

-- | Generate a fresh dictionary variable
freshDictVar :: MonadUnique m => m DictVar
freshDictVar = getUniqueM >>= return . FcTmVar . MkName (MkSym "d")

