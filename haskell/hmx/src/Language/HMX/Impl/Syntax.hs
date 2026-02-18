{-# LANGUAGE 
	KindSignatures,
	TypeFamilies,
 	GADTs,
	RankNTypes,
	DataKinds,
	DeriveTraversable,
	FlexibleInstances,
	KindSignatures,
	LambdaCase,
	PatternSynonyms,
	TemplateHaskell,
	OverloadedStrings
#-}

module Language.HMX.Impl.Syntax where

import qualified Control.Monad.Foil as Foil
import Control.Monad.Foil.TH
import Control.Monad.Free.Foil
import Control.Monad.Free.Foil.TH

import Data.ZipMatchK
-- import Data.ZipMatchK.Bifunctor ()
import Prelude (Integer, String)

import Data.Bifunctor.TH
import Generics.Kind.TH (deriveGenericK)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (fromString, IsString (..))

import qualified Language.HMX.Syntax.Abs    as HMX
import qualified Language.HMX.Syntax.Lex    as HMX
import qualified Language.HMX.Syntax.Par    as HMX
import qualified Language.HMX.Syntax.Print  as HMX
-- import Language.HMX.Impl.Constraint

import System.Exit (exitFailure)


mkSignature ''HMX.Expr ''HMX.VarIdent ''HMX.ScopedExpr ''HMX.Pattern

deriveGenericK ''ExprSig
deriveBifunctor ''ExprSig
deriveBifoldable ''ExprSig
deriveBitraversable ''ExprSig

-- What was before:
-- deriveZipMatch ''ExprSig
--
-- What happens now:
instance ZipMatchK Integer
instance ZipMatchK ExprSig

-- Pattern synonyms

mkPatternSynonyms ''ExprSig

{-# COMPLETE Var, EConstTrue, EConstFalse, EConstNat, EAdd, ESub, EIf, EIsZero, ETyped, ELet, ELam, EApp, EFor #-}

-- Conversion helpers

mkConvertToFreeFoil ''HMX.Expr ''HMX.VarIdent ''HMX.ScopedExpr ''HMX.Pattern
mkConvertFromFreeFoil ''HMX.Expr ''HMX.VarIdent ''HMX.ScopedExpr ''HMX.Pattern

-- Scope-safe patterns

mkFoilPattern ''HMX.VarIdent ''HMX.Pattern
deriveCoSinkable ''HMX.VarIdent ''HMX.Pattern
mkToFoilPattern ''HMX.VarIdent ''HMX.Pattern
mkFromFoilPattern ''HMX.VarIdent ''HMX.Pattern

-- Generated code (types)

-- Signature

mkSignature ''HMX.Type ''HMX.VarIdent ''HMX.ScopedType ''HMX.TypePattern

deriveGenericK ''TypeSig
deriveBifunctor ''TypeSig
deriveBifoldable ''TypeSig
deriveBitraversable ''TypeSig
instance ZipMatchK TypeSig

-- Pattern synonyms

mkPatternSynonyms ''TypeSig

{-# COMPLETE Var, TUVar, TNat, TBool, TFunc, TForAll #-}

-- Conversion helpers

mkConvertToFreeFoil ''HMX.Type ''HMX.VarIdent ''HMX.ScopedType ''HMX.TypePattern
mkConvertFromFreeFoil ''HMX.Type ''HMX.VarIdent ''HMX.ScopedType ''HMX.TypePattern

-- Scope-safe type patterns

mkFoilPattern ''HMX.VarIdent ''HMX.TypePattern
deriveCoSinkable ''HMX.VarIdent ''HMX.TypePattern
mkToFoilPattern ''HMX.VarIdent ''HMX.TypePattern
mkFromFoilPattern ''HMX.VarIdent ''HMX.TypePattern

-- User-defined Code

type Expr n = AST FoilPattern ExprSig n

type Type n = AST FoilTypePattern TypeSig n

type Type' = Type Foil.VoidS


-- Conversion helpers (expressions)

-- | Convert 'HMX.Exp' into a scope-safe expression.
-- This is a special case of 'convertToAST'.
toExpr :: (Foil.Distinct n) => Foil.Scope n -> Map HMX.VarIdent (Foil.Name n) -> HMX.Expr -> AST FoilPattern ExprSig n
toExpr = convertToAST convertToExprSig toFoilPattern getExprFromScopedExpr

-- | Convert 'HMX.Exp' into a closed scope-safe expression.
-- This is a special case of 'toExp'.
toExprClosed :: HMX.Expr -> Expr Foil.VoidS
toExprClosed = toExpr Foil.emptyScope Map.empty

-- | Convert a scope-safe representation back into 'HMX.Exp'.
-- This is a special case of 'convertFromAST'.
--
-- 'HMX.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromExpr :: Expr n -> HMX.Expr
fromExpr =
  convertFromAST
    convertFromExprSig
    HMX.EVar
    (fromFoilPattern mkIdent)
    HMX.ScopedExpr
    (\n -> HMX.VarIdent ("x" ++ show n))
  where
    mkIdent n = HMX.VarIdent ("x" ++ show n)

-- | Parse scope-safe terms via raw representation.
--
-- >>> fromString "let x = 2 + 2 in let y = x - 1 in let x = 3 in y + x + y" :: Expr Foil.VoidS
-- let x0 = 2 + 2 in let x1 = x0 - 1 in let x2 = 3 in x1 + x2 + x1
instance IsString (Expr Foil.VoidS) where
  fromString input = case HMX.pExpr (HMX.myLexer input) of
    Left err -> error ("could not parse expression: " <> input <> "\n  " <> err)
    Right term -> toExprClosed term

-- | Pretty-print scope-safe terms via"λ" Ident ":" Type "." Exrp1 raw representation.
instance Show (Expr n) where
  show = HMX.printTree . fromExpr

-- ** Conversion helpers (types)

-- | Convert 'HMX.Exp' into a scope-safe expression.
-- This is a special case of 'convertToAST'.
toType :: (Foil.Distinct n) => Foil.Scope n -> Map HMX.VarIdent (Foil.Name n) -> HMX.Type -> AST FoilTypePattern TypeSig n
toType = convertToAST convertToTypeSig toFoilTypePattern getTypeFromScopedType

-- | Convert 'HMX.Type' into a closed scope-safe expression.
-- This is a special case of 'toType'.
toTypeClosed :: HMX.Type -> Type Foil.VoidS
toTypeClosed = toType Foil.emptyScope Map.empty

-- | Convert a scope-safe representation back into 'HMX.Type'.
-- This is a special case of 'convertFromAST'.
--
-- 'HMX.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromType :: Type n -> HMX.Type
fromType =
  convertFromAST
    convertFromTypeSig
    HMX.TVar
    (fromFoilTypePattern mkIdent)
    HMX.ScopedType
    (\n -> HMX.VarIdent ("x" ++ show n))
  where
    mkIdent n = HMX.VarIdent ("x" ++ show n)

-- | Parse scope-safe terms via raw representation.
--
-- TODO: fix this example
-- -- >>> fromString "let x = 2 + 2 in let y = x - 1 in let x = 3 in y + x + y" :: Type Foil.VoidS
-- -- let x0 = 2 + 2 in let x1 = x0 - 1 in let x2 = 3 in x1 + x2 + x1
instance IsString (Type Foil.VoidS) where
  fromString input = case HMX.pType (HMX.myLexer input) of
    Left err -> error ("could not parse expression: " <> input <> "\n  " <> err)
    Right term -> toTypeClosed term

-- | Pretty-print scope-safe terms via"λ"VarIdent ":" Type "." Type1 raw representation.
instance Show (Type n) where
  show = HMX.printTree . fromType

instance Eq (Type Foil.VoidS) where
  (==) = alphaEquiv Foil.emptyScope


