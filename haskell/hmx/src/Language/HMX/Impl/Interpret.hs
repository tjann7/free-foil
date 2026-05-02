{-# LANGUAGE DataKinds #-}

module Language.HMX.Impl.Interpret where

import Control.Monad.Foil (S (VoidS), emptyScope)
import Language.HMX.Impl.Eval
import qualified Language.HMX.Syntax.Par as HMX
import qualified Language.HMX.Syntax.Abs as HMX
import qualified Language.HMX.Syntax.Lex as HMX

import Language.HMX.Impl.Syntax
import Language.HMX.Impl.Typecheck

import System.Exit (exitFailure)

data Result
  = Success (Expr VoidS, Type') -- Output of evaluation.
  | Failure ErrorKind String -- Error kind with message.
  deriving (Show)

data ErrorKind
  = TypecheckingError
  | EvaluationError
  deriving (Show)

-- | Interpret an HMX command.
interpretCommand :: HMX.Command -> Result
interpretCommand (HMX.CommandCompute expr) = case inferTypeNewClosed expr_ of
  Left err -> Failure TypecheckingError ("Typechecking error: " ++ err)
  Right type_ -> case eval emptyScope expr_ of
    Left err -> Failure EvaluationError ("Evaluation error: " ++ err)
    Right outExp -> Success (outExp, type_)
  where expr_ = toExprClosed expr 
interpretCommand (HMX.CommandCheck expr) = undefined

-- | Interpret an HMX program.
interpretProgram :: HMX.Program -> [String]
interpretProgram (HMX.Program commands) = map show (map interpretCommand commands)


defaultMain = do
  input <- getContents
  case HMX.pProgram (HMX.tokens input) of
    Left err -> do
      putStrLn "ERROR OCCURRED"
      putStrLn err
      exitFailure
    Right program -> do
      putStrLn "RIGHT PROGRAM"
      mapM_ putStrLn (interpretProgram program)

