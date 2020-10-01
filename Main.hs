{-# LANGUAGE LambdaCase #-}

module Main (main, runTest) where

import Frontend.HsParser      (hsParse)
import Frontend.HsRenamer     (hsRename)
import Frontend.HsTypeChecker (hsElaborate)
import Backend.FcTypeChecker  (fcTypeCheck)
import Backend.FcEvaluator    (fcEvaluate)

import Utils.Unique  (newUniqueSupply)
import Utils.PrettyPrint

import System.Environment (getArgs)

main :: IO ()
main = getArgs >>= \case
  [filename] -> runTest filename
  _other     -> putStrLn "Usage: ghc <filename>"

-- | Run a single testfile
runTest :: FilePath -> IO ()
runTest file = do
  -- Parsing
  hsParse file >>= \case
    Left err     -> throwMainError "parser" err
    Right ps_pgm -> do
      -- Renaming
      us0 <- newUniqueSupply 'u'
      case hsRename us0 ps_pgm of
        (Left err,_) -> throwMainError "renamer" err
        (Right (((rn_pgm, _rn_ctx), us1), rn_env), _) ->
          case hsElaborate rn_env us1 rn_pgm of
            (Left err,_) -> throwMainError "typechecker" err
            (Right ((((fc_pgm, tc_ty, theory), envs), us2), _tc_env), _) -> do
              putStrLn "---------------------------- Elaborated Program ---------------------------"
              putStrLn $ renderWithColor $ ppr fc_pgm
              putStrLn "------------------------------- Program Type ------------------------------"
              putStrLn $ renderWithColor $ ppr tc_ty
              putStrLn "------------------------------ Program Theory -----------------------------"
              putStrLn $ renderWithColor $ ppr theory
              case fcTypeCheck envs us2 fc_pgm of
                (Left err,_) -> throwMainError "System F typechecker" err
                (Right ((fc_ty, us3), _fc_env), _trace) -> do
                  putStrLn "-------------------------- System F Program Type --------------------------"
                  putStrLn $ renderWithColor $ ppr fc_ty
                  let res = fcEvaluate us3 fc_pgm
                  putStrLn "-------------------------- System F Result --------------------------------"
                  putStrLn $ renderWithColor $ ppr res

  where
    throwMainError phase e
      | label <- colorDoc red (text phase <+> text "failure")
      , msg   <- brackets label <+> colorDoc red (text e)
      = putStrLn (renderWithColor msg)

