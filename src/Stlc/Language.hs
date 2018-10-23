{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
module Stlc.Language where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)


-- All ids are Strings
type Id = String

type ShInfo = Set Id

-- Simple expressions in our language based on lambda calculus
data Exp = EVar Id                    -- "a", "b"
         | ELit Lit                   -- T/F
         | ELamSp Id Exp            -- \x -* ...
         | ELamSh Id Exp            -- \x ->> ...
         | EApp Exp Exp               -- e e'
         -- | ELet Id Exp Exp            -- Let x = e in e'
         -- For the time being becuase I do not want to mess around with polymorphism
         -- | EFix Exp Exp              -- letrec f \x. e
         -- and I do not want to mess with recursive functions (Though they should be seamless to add)
         deriving (Show, Eq, Ord)

data Lit = LitB Bool                  -- Literals for Bool
         | LitI Int                   -- Literals for Integer
         deriving (Show, Eq, Ord)

-- Some simple Expressions in our language

exp1 :: Exp
exp1 = EVar "a"        -- a

exp2 = ELamSp "a" exp1  -- \ a. a

litT = LitB True       -- True
litF = LitB False      -- False

lit0 = LitI 0        -- 0
lit1 = LitI 1        -- 1

-- \ x. (True x)
expInvalid :: Exp
expInvalid = ELamSp "x" (EApp (ELit litT) (EVar "x"))

-- Even though the above example is an expression it doesn't make sense
-- Q: How can we ensure we accept only those expressions that make sense?
-- A: Types to rescue

-- Types themselves are a language and they have syntax and semantics of their own

-- mono types i
data Iota = TBool                     -- Types for Booleans
          | TInt                      -- Types for Literals 1, 2, 3
          deriving (Show, Eq)

-- Other types
data Type = TVar Id                   -- Type variable
          | TArrSp Type Type          -- Arrow Type ->> Type
          | TArrSh Type Type          -- Arrow Type -* Type
          | TConst Iota               -- Concrete Type
          deriving (Show, Eq)

class FreeVariables a where
  fvs :: a -> Set Id

-- free type variables in some concrete type
-- > fvs (TArrSp (TVar "a") (TVar "b"))
-- fvs (a -> b)
-- fromList ["a","b"]
instance FreeVariables Type where
  fvs :: Type -> Set Id
  fvs (TVar i)     = Set.singleton i
  fvs (TArrSp t1 t2) = Set.union (fvs t1) (fvs t2)
  fvs (TArrSh t1 t2) = Set.union (fvs t1) (fvs t2)
  fvs (TConst _)   = Set.empty

-- Substitution for types is described as follows:
-- if its a type variable, just pick it out from the map
-- if it is a function, apply subsitution to both sides of the arrow
-- if it is const type, then we do not subtitute it with anything
instance Substitutable Type where
  substitute :: Substitution -> Type -> Type
  substitute (Subt m)     (TVar a)            = Map.findWithDefault (TVar a) a m
  substitute s            (TArrSp t1 t2)      = TArrSp (substitute s t1) (substitute s t2)
  substitute s            (TArrSh t1 t2)      = TArrSh (substitute s t1) (substitute s t2)
  substitute _            tcon@(TConst _)     = tcon

-- Scheme has a universal quantifier for types
-- Forall a, b, c TArrSp (TArrSp "a" "b") (TVar "c")
-- ∀ a,b,c. (a -> b) -> c
data Scheme = Forall (Set Id) Type
  deriving (Show, Eq)

scheme :: Type -> Scheme
scheme t = Forall (Set.empty) t

-- free type variables in a scheme are all the variables in the type
-- that are not quantified
-- > fvs (Forall (Set.singleton "a") (TArrSp (TVar "a") (TVar "b")))
-- fvs (∀a. a -> b)
-- fromList ["b"]
instance FreeVariables Scheme where
  fvs :: Scheme -> Set Id
  fvs (Forall is ty) = Set.difference (fvs ty) is

-- Substitue all the free variables in the type scheme with the substitution
instance Substitutable Scheme where
  substitute :: Substitution -> Scheme -> Scheme
  substitute (Subt s) sm@(Forall is ty) =
    Forall is (substitute (Subt (s `Map.restrictKeys` (fvs sm))) ty)

-- Q: How should we describe the substitution?
-- A: Substitution is nothing but a map from id to a type.
--    It is a process of replacing type of one term with another type
--    It will be used in specializing type variables in our typechecking algorithm
newtype Substitution = Subt (Map.Map Id Type)
  deriving (Show, Eq, Semigroup, Monoid)

sub :: Id -> Type -> Substitution
sub a t = Subt (Map.singleton a t)

class Substitutable a where
  substitute :: Substitution -> a -> a

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  substitute :: Substitution -> (a, b) -> (a, b)
  substitute s (x, y) = (substitute s x, substitute s y)

-- This means subsitution is composable (obviously)
-- if  a ---> b &&  b ---> c holds
--  ==>  a ---> c holds
instance Substitutable Substitution where
  substitute :: Substitution -> Substitution -> Substitution
  substitute s (Subt m) = Subt (fmap (substitute s) m)

-- Thrown when a type cannot be unified in unification function
data UnifyError = UnificationFailed String
  deriving (Show, Eq)

-- Gamma, context that contains all the typing judgements
-- It is a mapping of ids to their type schemes and variables they are in sharing with
-- gamma :: Context
-- gamma = Map.fromList [ ("add",
--                        Forall (Set.fromList ["a"])
--                        (TArrSp (TArrSp (TVar "a") (TVar "a")) (TVar "a"))
--                        [c, d],)
--                      ]
newtype Context =  Context (Map.Map Id (Scheme, Set Id))
  deriving (Show, Eq, Semigroup, Monoid)

getvars :: Context -> Set Id
getvars (Context c) = Set.fromList $ Map.keys c

-- get all the free variables from the context
-- this just goes over all the schemes and obtains the free variables from
-- each scheme and returns the union
instance FreeVariables Context where
  fvs :: Context -> Set Id
  fvs (Context m) = Set.unions (Map.elems $ Map.map (fvs . fst) m)

-- substitution on the sharing information is id (only becuase I am lazy and do not want to
-- deconstruct and re-construct the [id ---> (scheme, [ids])]
instance Substitutable ShInfo where
  substitute :: Substitution -> ShInfo -> ShInfo
  substitute _ ids = ids

-- Substitute the free variables in the context using the substitution
instance Substitutable Context where
  substitute :: Substitution -> Context -> Context
  substitute s (Context c) = Context (substitute s <$> c)


-- extend the context by adding an (id, scheme) pair
extendContext :: Context -> Id -> Scheme -> Set Id -> Context
extendContext (Context gamma) e ty ids = Context (Map.insert e (ty, ids) gamma)
