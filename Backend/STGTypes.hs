{-|
Module      : Backend.STGTypes
Description : Spineless Tagless G-Machine abstract syntax and pretty printing
Copyright   : Elias Storme, 2020
              Gert-Jan Bottu, 2020

Datatype declarations and pretty printing code for STG abstract syntax.
Based on definitions from the paper <https://www.microsoft.com/en-us/research/wp-content/uploads/1992/04/spineless-tagless-gmachine.pdf Peyton Jones, Simon. (1992). Implementing Lazy Functional Languages on Stock Hardware: The Spineless Tagless G-Machine.. J. Funct. Program.. 2. 127-202. 10.1017/S0956796800000319.> 
-}
module Backend.STGTypes where

import Utils.Var
import Utils.PrettyPrint

-- * Type Declarations
-- ** Programs
-- ----------------------------------------------------------------------------

-- | A program in the STG language.
-- A program is simply a collection of variable bindings. Its result is obtained by evaluating the global variable `main`.
newtype SProg = SProg SBinds

-- ** Variables and bindings
-- ----------------------------------------------------------------------------

-- | Variable
newtype SVar = SVar {svar_name :: Name}
-- | Constructor
newtype SCon = SCon {scon_clos :: SVar}

-- | Variable binding list
-- A list of bindings containing at least one element.
data SBinds = SBinds SBind (Maybe SBinds)
-- | Single variable binding
data SBind  = SBind  SVar SLForm

-- ** Expressions and atoms
-- ----------------------------------------------------------------------------

-- | Expression
data SExpr 
  = SLet  SBinds   SExpr  -- ^ Let expression
  | SLetR SBinds   SExpr  -- ^ Letrec expression
  | SCase SExpr    SAlts  -- ^ Case expression
  | SApp  SVar    [SAtom] -- ^ Application expression
  | SCApp SCon    [SAtom] -- ^ Fully saturated constructor application
  | SPApp SPrimOp [SAtom] -- ^ Fully saturated primitive operation application
  | SELit SLit            -- ^ Literal expression

-- | Atom
data SAtom = SVAt SVar | SLAt SLit

-- ** Case expression
-- ----------------------------------------------------------------------------

-- | Case alternatives
data SAlts
  = MkAAlts [SAAlt] SDefAlt -- ^ ADT alternatives 
  | MkPAlts [SPAlt] SDefAlt -- ^ Primitive alternatives

-- Algebraic alternative (over ADT)
data SAAlt   = SAAlt SCon [SVar] SExpr
-- Primitive alternative (over primitive literals)
data SPAlt   = SPAlt SLit SExpr
-- Default alternative
data SDefAlt = SDefAlt [SVar] SExpr

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

-- ** Primitive ops and literals
-- ----------------------------------------------------------------------------

-- | Primitive operations
data SPrimOp 
  = SAdd -- ^ Addition
  | SSub -- ^ Subtraction
  | SMul -- ^ Multiplication
  | SDiv -- ^ Division

-- | Wrapped literals
newtype SLit 
  = SLit Int -- ^ Wrapped integer

-- instance Symable SVar where
--   symOf = symOf . svar_name

-- Pretty printing
-- ----------------------------------------------------------------------------

instance PrettyPrint SExpr where
  ppr (SLet  bs  e  ) = hang (colorDoc yellow (text "let"))
                          2 (ppr bs)
                        $$
                        hang (colorDoc yellow (text "in"))
                          2 (ppr e)
  ppr (SLetR bs  e  ) = hang (colorDoc yellow (text "letrec"))
                          2 (ppr bs)
                        $$
                        hang (colorDoc yellow (text "in"))
                          2 (ppr e)
  ppr (SCase e   alt) = hang (colorDoc yellow (text "case") <+> ppr e <+> colorDoc yellow (text "of"))
                             2 (ppr alt)
  ppr (SApp  f   as ) = ppr f  <+> hsepmap ppr as
  ppr (SCApp c   as ) = ppr c  <+> hsepmap ppr as
  ppr (SPApp op  as ) = ppr op <+> hsepmap ppr as
  ppr (SELit lit    ) = ppr lit
  needsParens (SLet  _ _) = False
  needsParens (SLetR _ _) = False
  needsParens (SCase _ _) = False
  needsParens (SApp  _ _) = True
  needsParens (SCApp _ _) = True
  needsParens (SPApp _ _) = True
  needsParens (SELit _  ) = False

instance PrettyPrint SLForm where
  ppr (SLForm vfs u vas e) = hsepmap ppr vfs <+> ppr u <+> ppr vas <+> text "->" <+> ppr e
  needsParens = const True

instance PrettyPrint SUFlag where
  ppr Uble  = text "\\u"
  ppr NUble = text "\\n"
  needsParens = const False

instance PrettyPrint SBinds where
  ppr (SBinds vb bs) = ppr vb $$ ppr bs
  needsParens = const False

instance PrettyPrint SBind where
  ppr (SBind v lf) = ppr v <+> text "=" <+> ppr lf
  needsParens = const False 

instance PrettyPrint SAlts where
  ppr (MkAAlts as d) = vcat $ map ppr as ++ [ppr d]
  ppr (MkPAlts as d) = vcat $ map ppr as ++ [ppr d]
  needsParens = const False

instance PrettyPrint SAAlt where
  ppr (SAAlt c vs e) = ppr c <+> hcatmap ppr vs <+> text "->" <+> ppr e
  needsParens = const False

instance PrettyPrint SPAlt where
  ppr (SPAlt l e) = ppr l <+> text "->" <+> ppr e
  needsParens = const False

instance PrettyPrint SDefAlt where
  ppr (SDefAlt vs e) = pv <+> text "->" <+> ppr e
    where 
      pv = case vs of
        []  -> colorDoc green (text "default")
        _ -> hcatmap ppr vs
  needsParens = const False

instance PrettyPrint SAtom where
  ppr (SVAt v) = ppr v
  ppr (SLAt l) = ppr l
  needsParens = const False

instance PrettyPrint SVar where
  ppr           = ppr . svar_name
  needsParens = const False

instance PrettyPrint SCon where
  ppr           = ppr . scon_clos
  needsParens = const False 

instance PrettyPrint SLit where
  ppr (SLit i)  = int i <> text "#"
  needsParens = const False

instance PrettyPrint SPrimOp where
  ppr SAdd      = text "+#"
  ppr SSub      = text "-#"
  ppr SMul      = text "*#"
  ppr SDiv      = text "/#"
  needsParens = const False