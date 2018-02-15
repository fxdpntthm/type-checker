{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)


-- All ids are Strings
type Id = String

-- A unique id to identify a node in our syntax tree
type TId = Int

-- Simple expressions in our language based on lambda calculus

data Exp = EVar TId Id                    -- "a", "b"
         | ELit TId Lit                   -- T/F
         | ELam TId Id Exp               -- \x. ..
         | EApp TId Exp Exp               -- e e'
         | ELet TId Id Exp Exp           -- Let x = e in e'
         deriving (Show, Eq, Ord)

data Lit = LitB Bool                  -- Literals for Bool
         | LitInt Int                 -- Literals for Integer
         deriving (Show, Eq, Ord)

-- Some simple Expressions in our language

exp1 :: Exp
exp1 = EVar 1 "a"        -- a

exp2 = ELam 2 "a" exp1  -- \ a. a

litT = LitB True       -- True
litF = LitB False      -- False

lit0 = LitInt 0        -- 0
lit1 = LitInt 1        -- 1

-- \ x. (x True)
expInvalid :: Exp
expInvalid = ELam 1 "x" (EApp 2 (EVar 3 "x") (ELit 4 litT))

-- Even though the above example is an expression it doesn't make sense
-- Q: How can we ensure we accept only those expressions that make sense?

-- A: Types to rescue

-- Types themselves are a language and they have syntax and semantics of their own

-- mono types i
data Iota = TBool                     -- Types for Booleans
          | TInt                      -- Types for Literals 1, 2, 3
          deriving (Show, Eq)

-- Other concrete types
data Type = TVar Id                   -- Type variable
          | TArr Type Type            -- Arrow Type -> Type
          | TConst Iota               -- Concrete Type
          deriving (Show, Eq)

class FreeVariables a where
  fvs :: a -> Set Id

-- free type variables in some concrete type
-- > fvs (TArr (TVar "a") (TVar "b"))
-- fvs (a -> b)
-- fromList ["a","b"]
instance FreeVariables Type where
  fvs :: Type -> Set Id
  fvs (TVar i)     = Set.singleton i
  fvs (TArr t1 t2) = Set.union (fvs t1) (fvs t2)
  fvs (TConst _)   = Set.empty

-- Substitution for types is described as follows:
-- if its a type variable, just pick it out from the map
-- if it is a function, apply subsitution to both sides of the arrow
-- if it is const type, then we do not subtitute it with anything
instance Substitutable Type where
  substitute :: Type -> Substitution -> Type
  substitute (TVar a)          (Subt m)     = Map.findWithDefault (TVar a) a m
  substitute (TArr t1 t2)      s            = TArr (substitute t1 s) (substitute t2 s)
  substitute tcon@(TConst _)   _            = tcon

-- Scheme has a universal quantifier for types
-- Forall a, b, c TArr (TArr "a" "b") (TVar "c")
-- ∀ a,b,c (a -> b) -> c
data Scheme = Forall (Set Id) Type
  deriving (Show, Eq)

-- free type variables in a scheme are all the variables in the type
-- that are not quantified
-- > fvs (Forall (Set.singleton "a") (TArr (TVar "a") (TVar "b")))
-- fvs (∀a. a -> b)
-- fromList ["b"]
instance FreeVariables Scheme where
  fvs :: Scheme -> Set Id
  fvs (Forall is ty) = Set.difference (fvs ty) is

-- Substitue all the free variables in the type scheme with the substitution
instance Substitutable Scheme where
  substitute :: Scheme -> Substitution -> Scheme
  substitute sm@(Forall is ty) (Subt s) =
    Forall is (substitute ty (Subt (s `Map.restrictKeys` (fvs sm))))

-- Q: How should we describe the substitution?
-- A: Substitution is nothing but a map from id to a type.
--    It is a process of replacing type of one term with another type
--    It will be used in specializing type variables in our typechecking algorithm
newtype Substitution = Subt (Map.Map Id Type)
  deriving (Show, Eq, Monoid)

sub :: Id -> Type -> Substitution
sub a t = Subt (Map.singleton a t)

class Substitutable a where
  substitute :: a -> Substitution -> a

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  substitute :: (a, b) -> Substitution -> (a, b)
  substitute (x, y) s = (substitute x s, substitute y s)

-- This means subsitution is composable (obviously)
-- if  a ---> b &&  b ---> c holds
--  ==>  a ---> c holds
instance Substitutable Substitution where
  substitute :: Substitution -> Substitution -> Substitution
  substitute = mappend

data UnifyError = UnificationFailed String
  deriving (Show, Eq)

-- Gamma, context that contains all the typing judgements
-- It is a collection of terms to their types
-- gamma :: Context
-- gamma = Map.fromList [ ("add",
--                        Forall (Set.fromList ["a"])
--                        (TArr (TArr (TVar "a") (TVar "a")) (TVar "a")))
--                      ]
newtype Context =  Context (Map.Map Id Scheme)
  deriving (Show, Eq, Monoid)

-- get all the free variables from the context
-- this just goes over all the schemes and obtains the free variables from
-- each scheme and returns the union
instance FreeVariables Context where
  fvs :: Context -> Set Id
  fvs (Context m) = Set.unions (Map.elems $ Map.map fvs m)

-- Substitute all the free variables in the context using the substitution
instance Substitutable Context where
  substitute :: Context -> Substitution -> Context
  substitute (Context c) s = Context (flip (substitute) s <$> c)

-- extend the context by adding an (id, scheme) pair
updateContext :: Context -> Id -> Scheme -> Context
updateContext (Context gamma) e ty = Context (Map.insert e ty gamma)
