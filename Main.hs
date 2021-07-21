{-# LANGUAGE LambdaCase #-}

module Main (main, runTest) where

import Frontend.HsParser      (hsParse)
import Frontend.HsRenamer     (hsRename)
import Frontend.HsTypeChecker (hsElaborate)
import Optimizer.FcTypeChecker  (fcOptElaborate, fcResElaborate)
import Optimizer.FcPreprocessor (bindFreeOptTyVars, mergeAppAbsOptProg)
-- import Backend.Interpreter.FcEvaluator    (fcEvaluate)

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
            (Right ((((fc_opt_pgm, tc_ty, theory), envs), us2), _tc_env), _) -> do
              putStrLn "---------------------------- Elaborated Program ---------------------------"
              putStrLn $ renderWithColor $ ppr fc_opt_pgm
              putStrLn "------------------------ Elaborated, merged Program -----------------------"
              putStrLn $ renderWithColor $ ppr $ mergeAppAbsOptProg $ bindFreeOptTyVars fc_opt_pgm
              putStrLn "------------------------------- Program Type ------------------------------"
              putStrLn $ renderWithColor $ ppr tc_ty
              putStrLn "------------------------------ Program Theory -----------------------------"
              putStrLn $ renderWithColor $ ppr theory
              case fcOptElaborate envs us2 (mergeAppAbsOptProg $ bindFreeOptTyVars fc_opt_pgm) of
                (Left err,_) -> throwMainError "System F opt typechecker" err
                (Right (((fc_opt_ty, fc_res_pgm), us3), _fc_env), _trace) -> do
                  putStrLn "--------------------- System F Optimizer Program Type ---------------------"
                  putStrLn $ renderWithColor $ ppr fc_opt_ty
                  putStrLn "----------------------- System F Restricted Program -----------------------"
                  putStrLn $ renderWithColor $ ppr fc_res_pgm
                  case fcResElaborate envs us3 fc_res_pgm of
                    (Left err,_) -> throwMainError "System F res typechecker" err
                    (Right (((fc_res_ty, stg_pgm), us4), _fc_env), _trace) -> do
                      putStrLn "--------------------- System F Optimizer Program Type ---------------------"
                      putStrLn $ renderWithColor $ ppr fc_res_ty
                      putStrLn "------------------------------- STG Program -------------------------------"
                      putStrLn $ renderWithColor $ ppr stg_pgm
                  -- let res = fcEvaluate us3 fc_pgm
                  -- putStrLn "-------------------------- System F Result --------------------------------"
                  -- putStrLn $ renderWithColor $ ppr res

  where
    throwMainError phase e
      | label <- colorDoc red (text phase <+> text "failure")
      , msg   <- brackets label <+> colorDoc red (text e)
      = putStrLn (renderWithColor msg)

-- | Run a single testfile
writeSTG :: FilePath -> FilePath -> IO ()
writeSTG infile outfile = do
  -- Parsing
  hsParse infile >>= \case
    Left err     -> throwMainError "parser" err
    Right ps_pgm -> do
      -- Renaming
      us0 <- newUniqueSupply 'u'
      case hsRename us0 ps_pgm of
        (Left err,_) -> throwMainError "renamer" err
        (Right (((rn_pgm, _rn_ctx), us1), rn_env), _) ->
          case hsElaborate rn_env us1 rn_pgm of
            (Left err,_) -> throwMainError "typechecker" err
            (Right ((((fc_opt_pgm, tc_ty, theory), envs), us2), _tc_env), _) -> 
              case fcOptElaborate envs us2 (mergeAppAbsOptProg $ bindFreeOptTyVars fc_opt_pgm) of
                (Left err,_) -> throwMainError "System F opt typechecker" err
                (Right (((fc_opt_ty, fc_res_pgm), us3), _fc_env), _trace) -> 
                  case fcResElaborate envs us3 fc_res_pgm of
                    (Left err,_) -> throwMainError "System F res typechecker" err
                    (Right (((fc_res_ty, stg_pgm), us4), _fc_env), _trace) -> writeFile outfile (render $ ppr stg_pgm)

  where
    throwMainError phase e
      | label <- colorDoc red (text phase <+> text "failure")
      , msg   <- brackets label <+> colorDoc red (text e)
      = putStrLn (renderWithColor msg)