{-# LANGUAGE LambdaCase #-}

module Language.HMX.Impl.Eval where

import Control.Monad (forM)
import Control.Monad.Foil
  ( Distinct,
    Scope,
    addSubst,
    identitySubst,
  )
import Control.Monad.Free.Foil (AST (Var), substitute)
import Language.HMX.Impl.Syntax

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Control.Monad.Foil (emptyScope)

-- >>> eval emptyScope "if (iszero (2 - (1 + 1))) then true else 0"
-- Right "true"
-- >>> eval emptyScope "if (iszero (2 - (true + 1))) then true else 0"
-- Left "Unsupported expression in addition"
eval :: (Distinct n) => Scope n -> Expr n -> Either String (Expr n)
eval _scope (EVar x) = Right (EVar x)
eval _scope EConstTrue = Right EConstTrue
eval _scope EConstFalse = Right EConstFalse
eval _scope (EConstNat n) = Right (EConstNat n)
eval scope (EAdd l r) = do
  l' <- eval scope l
  r' <- eval scope r
  case (l', r') of
    (EConstNat x, EConstNat y) -> Right (EConstNat (x + y))
    _ -> Left "Unsupported expression in addition"
eval scope (ESub l r) = do
  l' <- eval scope l
  r' <- eval scope r
  case (l', r') of
    (EConstNat x, EConstNat y) -> Right (EConstNat (x - y))
    _ -> Left "Unsupported expression in subtraction"
eval scope (EIf cond then_ else_) = do
  cond' <- eval scope cond
  case cond' of
    EConstTrue -> eval scope then_
    EConstFalse -> eval scope else_
    _ -> Left "Unsupported condition in if statement"
eval scope (EIsZero n) =
  eval scope n >>= \case
    EConstNat n'
      | n' == 0 -> Right EConstTrue
      | otherwise -> Right EConstFalse
    _ -> Left "Unsupported expression in iszero"
eval scope (ETyped e _) = eval scope e
eval scope (ELet e1 (FoilPatternVar x) e2) = do
  e1' <- eval scope e1
  let subst = addSubst identitySubst x e1'
  eval scope (substitute scope subst e2)
eval _scope (ELam x e) = Right (ELam x e)
eval scope (EApp e1 e2) = do
  e1' <- eval scope e1
  e2' <- eval scope e2
  case e1' of
    ELam (FoilPatternVar x) e -> do
      let subst = addSubst identitySubst x e2'
      eval scope (substitute scope subst e)
    _ -> Left "Unsupported expression in application"
eval scope (EFor e1 e2 (FoilPatternVar x) expr) = do
  e1_val <- eval scope e1
  e2_val <- eval scope e2
  case (e1_val, e2_val) of
    (EConstNat from, EConstNat to) -> do
      let ys = [from .. to]
      results <- forM ys $ \y -> do
        let subst = addSubst identitySubst x (EConstNat y)
        eval scope (substitute scope subst expr)
      return (last results)
    _ -> Left "Invalid expression in the range of for-loop"
