module Backend.STGTypes where

import Utils.Var

-- * Programs and variable bindings
-- ----------------------------------------------------------------------------

newtype SProg = SProg SBinds

-- Variable
newtype SVar = SVar {svar_name :: Name}
newtype SCon = SCon SVar

-- Variable binding (non-empty list of bindings)
data SBinds = SBinds SVar SLForm SBinds
            | SBind  SVar SLForm

-- * Expressions and atoms
-- ----------------------------------------------------------------------------

-- Expression
data SExpr = SLet SBinds SExpr
           | SLetR SBinds SExpr
           | SCase SExpr SAlts
           | SApp SVar [SAtom]
           | SCApp SVar [SAtom]
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
                     }

-- Updatable flag
data SUFlag = Uble | NUble

-- * Primitive ops and literals
-- ----------------------------------------------------------------------------

-- Primitive operations
data SPrimOp = SAdd | SSub | SMul | SDiv

-- Wrapped literals
newtype SLit = SLit Int