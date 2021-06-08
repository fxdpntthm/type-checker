{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, PolyKinds #-}

module Stlc.Language where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (all, intersect)
import Data.Map (Map)
import Data.Set (Set)

type Id = String

data Phase = Parsed     
           | Freshened  
           | Tc         
           deriving (Show, Eq, Ord)

data Pass (p :: Phase)  -- What compiler pass are we in?
type PsPass = Pass 'Parsed
type FnPass = Pass 'Freshened
type TcPass = Pass 'Tc
  
-- Simple expressions in our language based on lambda calculus
data Exp pass =
    EVar (EId pass)                         -- "a", "b"
  | ELit Lit                                -- T/F
  | ELam (EId pass) (Exp pass)              -- \x. ..
  | EApp (Exp pass) (Exp pass)              -- e e'
  | ELet (EId pass) (Exp pass) (Exp pass)   -- Let x = e in e'
  | EFix (EId pass) (Exp pass)              -- letrec f \x. e
  | EIf (Exp pass) (Exp pass) (Exp pass)
--  deriving (Show, Eq, Ord)

data Lit = LitB Bool                  -- Literals for Bool
         | LitI Int                   -- Literals for Integer
         deriving (Eq, Ord)
instance Show Lit where
  show (LitB b) = show b
  show (LitI i) = show i

type ExpPs = Exp PsPass     -- Expression obtained after parsing      
type ExpFn = Exp FnPass     -- Expression obtained after name freshing
type ExpTc = Exp TcPass     -- Expression obtained after Type checking

type family EId a
type instance EId PsPass = String
type instance EId FnPass = Unique
type instance EId TcPass = TUnique

instance Show (EId (Pass p)) => Show (Exp (Pass p)) where
  show (EVar i) = show i
  show (ELit t) = show t
  show (ELam x b) = "\\ " ++ show x ++ " -> " ++ show b
  show (EApp e1 e2) = "(" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (ELet x e1 e2) = "let " ++ show x ++ " = " ++ show e1 ++ " in " ++ show e2
  show (EFix x e) = "letrec " ++ show x ++ " = " ++ show e
  show (EIf c e1 e2) = "if " ++ show c ++ " then " ++ show e1 ++ " else " ++ show e2
  
data Unique = Unique { value :: String, hash :: Int, scope :: Int }

instance Eq Unique where
  u1 == u2 = hash u1 == hash u2
instance Show Unique where
  show (Unique {value = v, scope = s}) = v ++ "`" ++ show s
instance Ord Unique where
  u1 <= u2 = hash u1 <= hash u2

data TUnique = TUnique { uq :: Unique, ty :: Type}
instance Eq TUnique where
  u1 == u2 = hash (uq u1) == hash (uq u2)
instance Show TUnique where
  show (TUnique {uq = u, ty = t}) = show u ++ "::" ++ show t
instance Ord TUnique where
  u1 <= u2 = hash (uq u1) <= hash (uq u2)

-- Some simple Expressions in our language

exp1, exp2 :: ExpPs
exp1 = EVar "a"        -- a

exp2 = ELam "a" exp1  -- \ a. a

litT, litF :: Lit
litT = LitB True       -- True
litF = LitB False      -- False

lit0, lit1 :: Lit
lit0 = LitI 0        -- 0
lit1 = LitI 1        -- 1

-- \ x. (True x)
expInvalid :: ExpPs
expInvalid = ELam "x" (EApp (ELit litT) (EVar "x"))

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
          | TArr Type Type            -- Arrow Type -> Type
          | TConst Iota               -- Concrete Type
          deriving (Eq)

instance Show Type where
  show (TVar i) = i
  show (TArr t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TConst TBool) = "Bool"
  show (TConst TInt) = "Int"

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
-- ∀ a,b,c. (a -> b) -> c
data Scheme = Forall (Set Id) Type
  deriving (Show, Eq)

scheme :: Type -> Scheme
scheme t = Forall (Set.empty) t

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
  deriving (Show, Eq, Semigroup, Monoid)

sub :: Id -> Type -> Substitution
sub a t = Subt (Map.singleton a t)

class Substitutable a where
  substitute :: a -> Substitution -> a

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  substitute :: (a, b) -> Substitution -> (a, b)
  substitute (x, y) s = (substitute x s, substitute y s)

consistent :: Substitution -> Substitution -> Bool
consistent (Subt m1) (Subt m2) = all (\v -> Map.lookup v m1 == Map.lookup v m2) vs  -- hyper efficient?
    where vs = intersect (Map.keys m1) (Map.keys m2)

-- This means subsitution is composable (obviously)
-- if  a ---> b &&  b ---> c holds
--  ==>  a ---> c holds
instance Substitutable Substitution where
  substitute :: Substitution -> Substitution -> Substitution
  substitute s s'@(Subt m) = if consistent s s'
                             then Subt (fmap (flip substitute s) m)
                             else error $ "Substituion is not composable for:\n\t" ++ show s ++ "\n\t" ++ show s' 

data UnifyError = UnificationFailed String
  deriving (Show, Eq)

-- Gamma, context that contains all the typing judgements
-- It is a collection of terms to their type schemes
-- gamma :: Context
-- gamma = Map.fromList [ ("add",
--                        Forall (Set.fromList ["a"])
--                        (TArr (TArr (TVar "a") (TVar "a")) (TVar "a")))
--                      ]
newtype Context =  Context (Map.Map Unique Scheme)
  deriving (Show, Eq, Semigroup, Monoid)

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
updateContext :: Context -> Unique -> Scheme -> Context
updateContext (Context gamma) e ty = Context (Map.insert e ty gamma)
