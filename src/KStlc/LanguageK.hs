{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

module KStlc.LanguageK where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)


-- All ids are Strings
type Id = String
------------------------------------------------------------
--                  EXPRESSIONS                           --
------------------------------------------------------------

-- Simple expressions in our language based on lambda calculus
data Exp = EVar Id                    -- "a", "b"
         | ELit Lit                   -- T/F
         | ELam Id Exp                -- \x. ..
         | EApp Exp Exp               -- e e'
         | ELet Id Exp Exp            -- Let x = e in e'
         | EFix Exp Exp              -- letrec f \x. e
         deriving (Show, Eq, Ord)

data Lit = LitB Bool                  -- Literals for Bool
         | LitI Int                   -- Literals for Integer
         deriving (Show, Eq, Ord)

-- Some simple Expressions in our language

exp1 :: Exp
exp1 = EVar "a"        -- a

exp2 = ELam "a" exp1  -- \ a. a

litT = LitB True       -- True
litF = LitB False      -- False

lit0 = LitI 0        -- 0
lit1 = LitI 1        -- 1

-- \ x. (True x)
expInvalid :: Exp
expInvalid = ELam "x" (EApp (ELit litT) (EVar "x"))

-- Even though the above example is an expression it doesn't make sense
-- Q: How can we ensure we accept only those expressions that make sense?
-- A: Types to rescue

------------------------------------------------------------
--                        KINDS                           --
------------------------------------------------------------

-- Kinds are useful for userdefined datatypes
-- It does not include lambda abstractions over kind
-- to keep the unification algorithm sane. Higher order kind
-- unification will make the type system undecidable
data Kind = KVar Id                     -- Kind Variable
          | KApp Kind Kind              -- Kind App t t
          | KStar                       -- Kind constant *
          deriving (Show, Eq)

instance Substitutable Kind where
  substitute :: Kind -> Substitution -> Kind
  substitute (KVar i) (Subst m)      = Map.findWithDefault (KVar i) i (snd m)
  substitute (KApp k1 k2)  s         = KApp (substitute k1 s) (substitute k2 s)
  substitute KStar _                 = KStar
------------------------------------------------------------
--                        TYPES                           --
------------------------------------------------------------
-- Types themselves are a language and they have syntax and semantics of their own

-- mono types i
data Iota = TBool                     -- Types for Booleans
          | TInt                      -- Types for Literals 1, 2, 3
          deriving (Show, Eq)

-- Other types
-- each type is sprinkled (annotated) with a kind
-- TVar will have a kind KVar becuase we don't know what type it is
-- TArr will Have a kind of * -> * -> *
-- TConst will have a kind of *
data Type = TVar Kind Id                   -- Type variable
          | TArr Kind Type Type            -- Arrow Type -> Type
          | TConst Kind Iota               -- Concrete Type
          | TCon Kind Id                   -- User defined Type constructor
          deriving (Show, Eq)

class FreeVariables a where
  fvs :: a -> Set Id

-- free type variables in some concrete type
-- > fvs (TArr (TVar "a") (TVar "b"))
-- fvs (a -> b)
-- fromList ["a","b"]
instance FreeVariables Type where
  fvs :: Type -> Set Id
  fvs (TVar _  i)     = Set.singleton i
  fvs (TArr _ t1 t2) = Set.union (fvs t1) (fvs t2)
  fvs (TConst _ _)   = Set.empty
  fvs (TCon _ _ )    = Set.empty

-- Substitution for types is described as follows:
-- if its a type variable, just pick it out from the map
-- if it is a function, apply subsitution to both sides of the arrow
-- if it is const type, then we do not subtitute it with anything
instance Substitutable Type where
  substitute :: Type -> Substitution -> Type
  substitute (TVar k a)          (Subt m)     = Map.findWithDefault (TVar k a) a (fst m)
  substitute (TArr k t1 t2)        s          = TArr k (substitute t1 s) (substitute t2 s)
  substitute tconst@(TConst _ _)   _          = tconst
  substitute tcon@(TCon _ _)       _          = tcon

-- Scheme has a universal quantifier for types
-- Forall a, b, c TArr (TArr "a" "b") (TVar "c")
-- ∀ a,b,c. (a -> b) -> c
data Scheme = Forall (Set Id) Type
  deriving (Show, Eq)

scheme :: Type -> Scheme
scheme t = Forall (Set.empty) t

data KScheme = KForall (Set Id) Kind
  deriving (Show, Eq)

-- free type variables in a scheme are all the variables in the type
-- that are not quantified
-- > fvs (Forall (Set.singleton "a") (TArr (TVar "a") (TVar "b")))
-- fvs (∀a. a -> b)
-- fromList ["b"]
instance FreeVariables Scheme where
  fvs :: Scheme -> Set Id
  fvs (Forall is _ ty) = Set.difference (fvs ty) is

-- Substitue all the free variables in the type scheme with the substitution
instance Substitutable Scheme where
  substitute :: Scheme -> Substitution -> Scheme
  substitute sm@(Forall is k ty) (Subt s) =
    Forall is (substitute k ((snd s) `Map.restrictKeys`)) (substitute ty (Subt ((fst s) `Map.restrictKeys` (fvs sm))))

-- Q: How should we describe the substitution?
-- A: Substitution is nothing but a map from id to a type.
--    It is a process of replacing type of one term with another type
--    It will be used in specializing type variables in our typechecking algorithm
newtype Substitution = Subt ((Map.Map Id Type), (Map.Map Id Kind))
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
  substitute s (Subt m) = Subt (fmap (flip substitute s) m)

data UnifyError = UnificationFailed String
  deriving (Show, Eq)

-- Gamma, context that contains all the typing judgements
-- It is a collection of terms to their type schemes
-- gamma :: Context
-- gamma = Map.fromList [ ("add",
--                        Forall (Set.fromList ["a"])
--                        (TArr (TArr (TVar "a") (TVar "a")) (TVar "a")))
--                      ]
newtype Context =  Context (Map.Map Id Scheme)
  deriving (Show, Eq, Monoid)

newtype KContext = KContext (Map.Map Id KScheme)
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
