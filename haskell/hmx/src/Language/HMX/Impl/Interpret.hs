{-# LANGUAGE DataKinds #-}

module Language.HMX.Impl.Interpret where

import Control.Monad.Foil (S (VoidS), emptyScope)
import Language.HMX.Impl.Eval
import qualified Language.HMX.Syntax.Par as HMX
import qualified Language.HMX.Syntax.Abs as HMX
import Language.HMX.Impl.Syntax
import Language.HMX.Impl.Typecheck

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
interpretCommand (HMX.CommandCompute expr) = case inferTypeNewClosed expr of
  Left err -> Failure TypecheckingError ("Typechecking error: " ++ err)
  Right type_ -> case eval emptyScope expr of
    Left err -> Failure EvaluationError ("Evaluation error: " ++ err)
    Right outExp -> Success (outExp, type_)
interpretCommand (HMX.CommandCheck expr) = undefined

-- | Interpret an HMX program.
interpretProgram :: HMX.Program -> IO ()
interpretProgram (HMX.Program commands) = mapM_ interpretCommand commands


defaultMain :: IO ()
defaultMain = undefined
--defaultMain = do
--  input <- getContents
--  case HMX.pProgram (HMX.resolveLayout True (HMX.tokens input)) of
--    Left err -> do
--      putStrLn err
--      exitFailure
--    Right program -> interpretProgram program

