{-# LANGUAGE GADTs ,
		TemplateHaskell
#-}

module Language.HMX.Impl.Constraint where

import qualified Language.HMX.Syntax.Abs    as HMX
import qualified Language.HMX.Syntax.Lex    as HMX
import qualified Language.HMX.Syntax.Par    as HMX
import qualified Language.HMX.Syntax.Print  as HMX

import System.Exit (exitFailure)



data MonoType var
  = Var var
--  | Tuple [MonoType var]
--  | SumType (MonoType var) (MonoType var)
--  | Record [(String, MonoType var)]

-- Type Scheme
data PolyType constraint type var
  = TypeForall [var] [constraint type var] (type var)
  -- forall a b. (Eq a, Show b) => [a] -> b

data CEq type var
  = CEq (type var) (type var)

data CEqError type var
  = UnexpectTypeError (type var) (type var)

data CSubType type var
  = CSubType (type var) (type var)

data CTypeClass type var
  = CTypeClass ClassName [type var]
  deriving (Functor)

data Subst type a = Subst [(a, type a)]

-- | Instances of this class should have principle normal form property.
class ConstraintSystem e x where
  substInConstraint :: Functor type => (a -> type b) -> x type a -> x type b
  renameInConstraint :: Functor type => (a -> b) -> x type a -> x type b
  -- reduceStep :: Functor type => [x type a] -> Either e (x type a)
  normalize :: Functor type => [x type a] -> Subst a (type a) -> Either e ([x type a], Subst a (type a))

instance ConstraintSystem CEqError CEq where
  ...

