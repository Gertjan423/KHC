module Backend.STGTypes where

import Utils.Var
import Utils.PrettyPrint

-- * Programs and variable bindings
-- ----------------------------------------------------------------------------

newtype SProg = SProg SBinds

-- Variable
newtype SVar = SVar {svar_name :: Name}
newtype SCon = SCon {scon_clos :: SVar}

-- Variable binding (non-empty list of bindings)
data SBinds = SBinds SVar SLForm SBinds
            | SBind  SVar SLForm

-- * Expressions and atoms
-- ----------------------------------------------------------------------------

-- Expression
data SExpr = SLet  SBinds   SExpr
           | SLetR SBinds   SExpr
           | SCase SExpr    SAlts
           | SApp  SVar    [SAtom]
           | SCApp SCon    [SAtom]
           | SPApp SPrimOp [SAtom]
           | SELit SLit

-- Atoms
data SAtom = SVAt SVar | SLAt SLit

-- * Case expression
-- ----------------------------------------------------------------------------

-- Case alternatives
data SAlts = MkAAlts [SAAlt] SDefAlt -- algebraic alternative
           | MkPAlts [SPAlt] SDefAlt

-- Algebraic alternative (over ADT)
data SAAlt   = SAAlt SCon [SVar] SExpr
-- Primitive alternative (over primitive literals)
data SPAlt   = SPAlt SLit SExpr
-- Default alternative
data SDefAlt = SDefAlt [SVar] SExpr

-- * Lambda form
-- ----------------------------------------------------------------------------

-- Lambda form
data SLForm = SLForm { slform_var_free :: [SVar]    -- Free variables
                     , slform_upd_flag :: SUFlag    -- Update flag
                     , slform_var_attr :: [SVar]    -- Lambda attributes
                     , slform_exp      :: SExpr     -- Lambda body
                     }

-- Updatable flag
data SUFlag = Uble | NUble

-- * Primitive ops and literals
-- ----------------------------------------------------------------------------

-- Primitive operations
data SPrimOp = SAdd | SSub | SMul | SDiv

-- Wrapped literals
newtype SLit = SLit Int

-- * Pretty Printing
-- ------------------------------------------------------------------------------

-- instance Symable SVar where
--   symOf = symOf . svar_name

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

-- | Pretty print variable bindings
instance PrettyPrint SBinds where
  ppr (SBinds v lf bs) = ppr (SBind v lf) $$ ppr bs
  ppr (SBind  v lf   ) = ppr v <+> text "=" <+> ppr lf
  needsParens = const False

-- | Pretty print case alternatives
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


-- | Pretty print atoms, variables and constructors
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

-- | Pretty print primitive literals and operators
instance PrettyPrint SLit where
  ppr (SLit i)  = int i <> text "#"
  needsParens = const False

instance PrettyPrint SPrimOp where
  ppr SAdd      = text "+#"
  ppr SSub      = text "-#"
  ppr SMul      = text "*#"
  ppr SDiv      = text "/#"
  needsParens = const False