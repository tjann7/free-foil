module Language.HMX.Impl.Interpret where

import Control.Monad.Foil (S (VoidS), emptyScope)
import Language.HMX.Impl.Eval
import Language.HMX.Impl.Parser.Par
import Language.HMX.Impl.Syntax (Expr, Type', toExpClosed)
import Language.HMX.Impl.Typecheck

data Result
  = Success (Expr VoidS, Type') -- Output of evaluation.
  | Failure ErrorKind String -- Error kind with message.
  deriving (Show)

data ErrorKind
  = ParsingError
  | TypecheckingError
  | EvaluationError
  deriving (Show)

--interpret :: String -> Result
--interpret input =
--  case toExpClosed <$> pExpr tokens of
--    Left err -> Failure ParsingError ("Parsing error: " ++ err)
--    Right e -> case inferTypeNewClosed e of
--      Left err -> Failure TypecheckingError ("Typechecking error: " ++ err)
--      Right type_ -> case eval emptyScope e of
--        Left err -> Failure EvaluationError ("Evaluation error: " ++ err)
--        Right outExpr -> Success (outExpr, type_)
--  where
--    tokens = myLexer input

--whnf :: EApp -> Expr
--whnf (EApp loc_ expr1 expr2) = case expr1 of
--  ELam loc_ (PatternVar loc_ (VarIdent)) Expr -> undefined
    

-- | Interpret an HMX command.
interpretCommand :: HMX.Command -> IO ()
interpretCommand (HMX.CommandCompute _loc expr) = case eval emptyScope expr of
  Left err -> Failure EvaluationError ("Evaluation error: " ++ err)
  Right outExpr -> Success (outExpr, (Type' "NONE"))
interpretCommand (HMX.CommandCheck _loc expr) = inferTypeNewClosed expr

-- | Interpret an HMX program.
interpretProgram :: HMX.Program -> IO ()
interpretProgram (HMX.AProgram _loc commands) = mapM_ interpretCommand commands


defaultMain :: IO ()
defaultMain = undefined
--defaultMain = do
--  input <- getContents
--  case HMX.pProgram (HMX.resolveLayout True (HMX.tokens input)) of
--    Left err -> do
--      putStrLn err
--      exitFailure
--    Right program -> interpretProgram program

