{-# LANGUAGE FlexibleContexts #-}

module Utils.Errors where

import Utils.PrettyPrint
import Control.Monad.Except

-- GEORGE: Store a doc as an error, not a string
throwErrorM :: MonadError String m => Doc -> m a
throwErrorM d = throwError (renderError d)

throwUnimplErrorM :: MonadError String m => m a
throwUnimplErrorM = throwErrorM $ text "Unimplemented."