{-# LANGUAGE FlexibleContexts #-}

module Utils.Trace (Trace, traceM, dumpTrace) where

import Utils.PrettyPrint
import Utils.SnocList
import Control.Monad.Writer

newtype Trace = MkTrace (SnocList Doc)

instance Monoid Trace where
  mempty  = MkTrace mempty
  mappend (MkTrace t1) (MkTrace t2) = MkTrace (mappend t1 t2)
  mconcat ts = MkTrace $ mconcat [t | MkTrace t <- ts]

dumpTrace :: Trace -> Doc
dumpTrace (MkTrace t) = go t
  where
    go SN        = empty
    go (ds :> d) = go ds $$ d

traceM :: MonadWriter Trace m => String -> Doc -> m ()
traceM fun d = tell (MkTrace (SN :> (text fun <+> colon <+> d)))

