{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}
module Language.HMX.Impl.FreeFoil where

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor.Sum
import           Data.Bifunctor.TH
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.ZipMatchK
import           Data.String                     (IsString (..))
import           Generics.Kind.TH                (deriveGenericK)
import qualified Language.HMX.Syntax.Abs    as Raw
import qualified Language.HMX.Syntax.Layout as Raw
import qualified Language.HMX.Syntax.Lex    as Raw
import qualified Language.HMX.Syntax.Par    as Raw
import qualified Language.HMX.Syntax.Print  as Raw
import           System.Exit                     (exitFailure)
import Data.ZipMatchK.Bifunctor ()

-- $setup
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds

-- | The signature 'Bifunctor' for the HM(X).
data HMXF scope term
  = AppF term term        -- ^ Application: \((t_1 \; t_2)\)
  | LamF scope            -- ^ Abstraction: \(\lambda x. t\)
  deriving (Eq, Show, Functor, Foldable, Traversable)
deriveBifunctor ''HMXF
deriveBifoldable ''HMXF
deriveBitraversable ''HMXF
deriveGenericK ''HMXF
instance ZipMatchK HMXF

-- | HM(X)-terms in scope @n@, freely generated from the sum of signatures 'HMXF' and t'PairF'.
type HMX n = AST Foil.NameBinder HMXF n

pattern App :: HMX n -> HMX n -> HMX n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: Foil.NameBinder n l -> HMX l -> HMX n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

{-# COMPLETE Var, App, Lam #-}

-- | HM(X)-terms are pretty-printed using BNFC-generated printer via 'Raw.Term'.
instance Show (HMX Foil.VoidS) where
  show = ppHMX

-- | HM(X)-terms can be (unsafely) parsed from a 'String' via 'Raw.Term'.
instance IsString (HMX Foil.VoidS) where
  fromString input =
    case Raw.pTerm (Raw.tokens input) of
      Left err -> error ("could not parse HM(x)-term: " <> input <> "\n  " <> err)
      Right term -> toHMXClosed term

-- | Compute weak head normal form (WHNF) of a HM(X)-term.
--
-- >>> whnf Foil.emptyScope "(λx.(λ_.x)(λy.x))(λy.λz.z)"
-- λ x0 . λ x1 . x1
--
-- >>> whnf Foil.emptyScope "(λs.λz.s(s(z)))(λs.λz.s(s(z)))"
-- λ x1 . (λ x0 . λ x1 . x0 (x0 x1)) ((λ x0 . λ x1 . x0 (x0 x1)) x1)
--
-- Note that during computation bound variables can become unordered
-- in the sense that binders may easily repeat or decrease. For example,
-- in the following expression, inner binder has lower index that the outer one:
--
-- >>> whnf Foil.emptyScope "(λx.λy.x)(λx.x)"
-- λ x1 . λ x0 . x0
--
-- At the same time, without substitution, we get regular, increasing binder indices:
--
-- >>> "λx.λy.y" :: HMX Foil.VoidS
-- λ x0 . λ x1 . x1
--
-- To compare terms for \(\alpha\)-equivalence, we may use 'alphaEquiv':
--
-- >>> alphaEquiv Foil.emptyScope (whnf Foil.emptyScope "(λx.λy.x)(λx.x)") "λx.λy.y"
-- True
--
-- We may also normalize binders using 'refreshAST':
--
-- >>> refreshAST Foil.emptyScope (whnf Foil.emptyScope "(λx.λy.x)(λx.x)")
-- λ x0 . λ x1 . x1
whnf :: Foil.Distinct n => Foil.Scope n -> HMX n -> HMX n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = Foil.addSubst Foil.identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

-- | Convert a raw \(\lambda\)-abstraction into a scope-safe HM(X)-term.
toHMXLam
  :: Foil.Distinct n
  => Foil.Scope n                   -- ^ Target scope of the HM(X)-term.
  -> Map Raw.VarIdent (Foil.Name n) -- ^ Mapping for the free variables in the raw term.
  -> Raw.Pattern                    -- ^ Raw pattern (argument) of the \(\lambda\)-abstraction.
  -> Raw.ScopedTerm                 -- ^ Raw body of the \(\lambda\)-abstraction.
  -> HMX n
toHMXLam scope env pat (Raw.AScopedTerm _loc body) =
  case pat of
    Raw.PatternVar _loc x -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
          env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
       in Lam binder (toHMX scope' env' body)

-- | Convert a raw expression into a scope-safe HM(X)-term.
toHMX
  :: Foil.Distinct n
  => Foil.Scope n                   -- ^ Target scope of the HM(X)-term.
  -> Map Raw.VarIdent (Foil.Name n) -- ^ Mapping for the free variables in the raw term.
  -> Raw.Term                       -- ^ Raw expression or type.
  -> HMX n
toHMX scope env = \case
  Raw.Var _loc x ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing   -> error ("unbound variable: " ++ Raw.printTree x)

  Raw.App _loc fun arg ->
    App (toHMX scope env fun) (toHMX scope env arg)

  Raw.Lam _loc pat body -> toHMXLam scope env pat body

-- | Convert a raw expression into a /closed/ scope-safe HM(X)-term.
toHMXClosed :: Raw.Term -> HMX Foil.VoidS
toHMXClosed = toHMX Foil.emptyScope Map.empty

-- | Convert back from a scope-safe HM(X)-term into a raw expression or type.
fromHMX
  :: [Raw.VarIdent]               -- ^ Stream of fresh raw identifiers.
  -> Foil.NameMap n Raw.VarIdent  -- ^ A /total/ map for all names in scope @n@.
  -> HMX n                   -- ^ A scope-safe HM(X)-term.
  -> Raw.Term
fromHMX freshVars env = \case
  Var name -> Raw.Var loc (Foil.lookupName name env)
  App fun arg -> Raw.App loc (fromHMX freshVars env fun) (fromHMX freshVars env arg)
  Lam binder body ->
    case freshVars of
      [] -> error "not enough fresh variables"
      x:freshVars' ->
        let env' = Foil.addNameBinder binder x env
         in Raw.Lam loc (Raw.PatternVar loc x) (Raw.AScopedTerm loc (fromHMX freshVars' env' body))
  where
    loc = error "no location info available when converting from an AST"

-- | Convert back from a scope-safe HM(X)-term into a raw expression or type.
--
-- In contrast to 'fromHMX', this function uses the raw foil identifiers (integers)
-- to generate names for the variables. This makes them transparent when printing.
fromHMX'
  :: HMX n                   -- ^ A scope-safe HM(X)-term.
  -> Raw.Term
fromHMX' = \case
  Var name -> Raw.Var loc (ppName name)
  App fun arg -> Raw.App loc (fromHMX' fun) (fromHMX' arg)
  Lam binder body ->
    let x = ppName (Foil.nameOf binder)
     in Raw.Lam loc (Raw.PatternVar loc x) (Raw.AScopedTerm loc (fromHMX' body))
  where
    loc = error "no location info available when converting from an AST"
    ppName name = Raw.VarIdent ("x" ++ show (Foil.nameId name))

-- | Pretty-print a /closed/ HM(X)-term.
ppHMX :: HMX Foil.VoidS -> String
ppHMX = Raw.printTree . fromHMX'

-- | Interpret a HM(X) command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute _loc term _type) =
      putStrLn ("  ↦ " ++ ppHMX (whnf Foil.emptyScope (toHMX Foil.emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _loc _term _type) = putStrLn "check is not yet implemented"

-- | Interpret a HM(X) program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram _loc typedTerms) = mapM_ interpretCommand typedTerms

-- | A HM(X) interpreter implemented via the free foil.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case Raw.pProgram (Raw.resolveLayout True (Raw.tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
