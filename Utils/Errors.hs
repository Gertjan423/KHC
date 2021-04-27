{-# LANGUAGE FlexibleContexts #-}

module Utils.Errors where

import Utils.PrettyPrint
import Control.Monad.Except

-- GEORGE: Store a doc as an error, not a string
throwErrorM :: MonadError String m => Doc -> m a
throwErrorM d = throwError (renderError d)

throwUnimplErrorM :: MonadError String m => m a
throwUnimplErrorM = throwErrorM $ text "Unimplemented."

-- | Throw an error indicating a type isn't what it should be
-- |   loc_m indicates the error location, err_m is the error message
-- |   err_t gives more info about the type printed
throwUnTyErrorM :: (MonadError String m, PrettyPrint b) => String -> String -> String -> b -> m a
throwUnTyErrorM loc_m err_m err_t ty = throwErrorM (text loc_m <+> colon <+> text err_m
                $$ text err_t <+> ppr ty)

-- | Throw an error indicating two types don't match where they should
-- |   loc_m indicates the error location, err_m is the error message
throwBinTyErrorM :: (MonadError String m, PrettyPrint b) => String -> String -> b -> b -> m a
throwBinTyErrorM loc_m err_m ty1 ty2 = throwErrorM (text loc_m <+> colon <+> text err_m
                $$ text "declared:" <+> ppr ty1 
                $$ text "inferred:" <+> ppr ty2)