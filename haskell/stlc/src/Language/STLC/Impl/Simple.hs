
module Language.STLC.Impl.Simple where

import qualified Language.STLC.Syntax.Abs    as STLC
import qualified Language.STLC.Syntax.Layout as STLC
import qualified Language.STLC.Syntax.Lex    as STLC
import qualified Language.STLC.Syntax.Par    as STLC
import qualified Language.STLC.Syntax.Print  as STLC

import System.Exit (exitFailure)


whnf :: EApp -> Expr
whnf (EApp loc_ expr1 expr2) = case expr1 of
    ELam loc_ (PatternVar loc_ (VarIdent)) Expr -> 
      Var
    _ -> 
    

-- | Interpret an STLC command.
interpretCommand :: STLC.Command -> IO ()
interpretCommand (STLC.CommandCompute _loc expr) = undefined
interpretCommand (STLC.CommandCheck _loc expr) = undefined

-- | Interpret an STLC program.
interpretProgram :: STLC.Program -> IO ()
interpretProgram (STLC.AProgram _loc commands) = mapM_ interpretCommand commands


defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case STLC.pProgram (STLC.resolveLayout True (STLC.tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program

