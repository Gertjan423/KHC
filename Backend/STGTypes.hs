{-|
Module      : Backend.STGTypes
Description : Spineless Tagless G-Machine abstract syntax and pretty printing
Copyright   : Elias Storme, 2020
              Gert-Jan Bottu, 2020

Datatype declarations and pretty printing code for STG abstract syntax.
Based on definitions from the paper <https://www.microsoft.com/en-us/research/wp-content/uploads/1992/04/spineless-tagless-gmachine.pdf Peyton Jones, Simon. (1992). Implementing Lazy Functional Languages on Stock Hardware: The Spineless Tagless G-Machine.. J. Funct. Program.. 2. 127-202. 10.1017/S0956796800000319.> 
-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Backend.STGTypes where

import Utils.Var
import Utils.PrettyPrint
import Utils.Prim
import Utils.Unique (stgBoxedIntConUnique, stgPatternMatchErrorUnique)

-- * Type Declarations
-- ** Programs
-- ----------------------------------------------------------------------------

-- | A program in the STG language.
-- A program is simply a collection of variable bindings. Its result is obtained by evaluating the global variable `main`.
newtype SProg = SProg [SBind]

-- ** Variables and bindings
-- ----------------------------------------------------------------------------

-- | Constructor
newtype SCon = SCon {scon_name :: Name}

instance Symable SCon where
  symOf = symOf . scon_name

mkStgBoxedIntCon :: SCon
mkStgBoxedIntCon = SCon stgBoxedIntConName

stgBoxedIntConName :: Name
stgBoxedIntConName = mkName (mkSym "MkInt") stgBoxedIntConUnique

mkStgPatternMatchErrorCon :: SCon
mkStgPatternMatchErrorCon = SCon stgPatternMatchErrorConName

stgPatternMatchErrorConName :: Name
stgPatternMatchErrorConName = mkName (mkSym "PatternMatchError") stgPatternMatchErrorUnique

-- | Variable binding list
-- A list of bindings containing at least one element.
-- data SBinds = SBinds SBind (Maybe SBinds)
-- | Variable binding
data SBind  = SBind  SVar SLForm

-- | Smart constructor for list of STG binds
sBinds :: [SVar] -> [SLForm] -> [SBind]
sBinds = zipWith SBind

-- ** Expressions and atoms
-- ----------------------------------------------------------------------------

-- | Expression
data SExpr 
  = SLet  [SBind]  SExpr  -- ^ Let expression (mutually recursive)
  | SCase SExpr    SAlts  -- ^ Case expression
  | SApp  SVar     SAtoms -- ^ Application to variable
  | SCApp SCon     SAtoms -- ^ Fully saturated constructor application
  | SPApp PrimOp   SAtoms -- ^ Fully saturated primitive operation application
  | SELit PrimLit         -- ^ Literal expression

-- | Atom, and list of atoms
data SAtom = SAtVar SVar | SAtLit PrimLit
type SAtoms = [SAtom]


-- ** Case expression
-- ----------------------------------------------------------------------------

-- | Case alternatives
data SAlts
  = SAAlts [SAAlt] SDefAlt -- ^ ADT alternatives 
  | SPAlts [SPAlt] SDefAlt -- ^ Primitive alternatives

-- Algebraic alternative (over ADT)
data SAAlt   = SAAlt SCon [SVar] SExpr
-- Primitive alternative (over primitive literals)
data SPAlt   = SPAlt PrimLit SExpr
-- Default alternative
data SDefAlt = SDefBound SVar SExpr
             | SDefUnbound SExpr

mkStgErrorDefAlt :: SDefAlt
mkStgErrorDefAlt = SDefUnbound (SCApp mkStgPatternMatchErrorCon [])

-- ** Lambda form
-- ----------------------------------------------------------------------------

-- | Lambda form
data SLForm = SLForm { slform_var_free :: [SVar]    -- ^ Free variables
                     , slform_upd_flag :: SUFlag    -- ^ Update flag
                     , slform_var_attr :: [SVar]    -- ^ Lambda attributes
                     , slform_exp      :: SExpr     -- ^ Lambda body
                     }

-- | Update flag
data SUFlag 
  = Uble  -- ^ Updatable
  | NUble -- ^ Not Updatable

-- Pretty printing
-- ----------------------------------------------------------------------------

instance PrettyPrint SProg where
  ppr (SProg binds) = fsep $ map ((<+>) (text "define") . (terminate semi) . ppr) binds
  needsParens _     = False

instance PrettyPrint SExpr where
  ppr (SLet  bs  e  ) = hang (colorDoc yellow (text "let"))
                          2 (fsep $ map (terminate semi . ppr) bs)
                        $$
                        hang (colorDoc yellow (text "in"))
                          2 (ppr e)
  ppr (SCase e   alt) = hang (colorDoc yellow (text "case") <+> ppr e <+> colorDoc yellow (text "of"))
                             2 (ppr alt)
  ppr (SApp  f   as ) = ppr f  <+> ppr as
  ppr (SCApp c   as ) = ppr c  <+> ppr as
  ppr (SPApp op  as ) = ppr op <+> ppr as
  ppr (SELit lit    ) = ppr lit
  needsParens (SLet  _ _) = False
  needsParens (SCase _ _) = False
  needsParens (SApp  _ _) = True
  needsParens (SCApp _ _) = True
  needsParens (SPApp _ _) = True
  needsParens (SELit _  ) = False

instance PrettyPrint SLForm where
  ppr (SLForm vfs u vas e) = ppr vfs <+> ppr u <+> ppr vas <+> text "->" <+> ppr e
  needsParens = const True

instance PrettyPrint SUFlag where
  ppr Uble  = text "\\u"
  ppr NUble = text "\\n"
  needsParens = const False

instance PrettyPrint SBind where
  ppr (SBind v lf) = ppr v <+> text "=" <+> ppr lf
  needsParens = const False 

instance PrettyPrint SAlts where
  ppr (SAAlts as d) = vcat $ map (terminate semi . ppr) as ++ [ppr d]
  ppr (SPAlts as d) = vcat $ map (terminate semi . ppr) as ++ [ppr d]
  needsParens = const False

instance PrettyPrint SAAlt where
  ppr (SAAlt c vs e) = ppr c <+> ppr vs <+> text "->" <+> ppr e
  needsParens = const False

instance PrettyPrint SPAlt where
  ppr (SPAlt l e) = ppr l <+> text "->" <+> ppr e
  needsParens = const False

instance PrettyPrint SDefAlt where
  ppr (SDefBound v e) = ppr v <+> text "->" <+> ppr e
  ppr (SDefUnbound e) = colorDoc green (text "default") <+> text "->" <+> ppr e
  needsParens = const False

instance {-# OVERLAPS #-} PrettyPrint SAtoms where
  ppr = braces . fsep . punctuate comma . map ppr
  needsParens = const False

instance PrettyPrint SAtom where
  ppr (SAtVar v) = ppr v
  ppr (SAtLit l) = ppr l
  needsParens = const False

instance PrettyPrint SCon where
  ppr           = ppr . symOf
  needsParens = const False 