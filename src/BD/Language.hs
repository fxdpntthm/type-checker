{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, PolyKinds #-}

module BD.Language where

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
  show (Unique {value = v}) = v
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
  substitute :: Substitution -> Type -> Type
  substitute (Subt m)     (TVar a)         = Map.findWithDefault (TVar a) a m
  substitute  s           (TArr t1 t2)     = TArr (substitute s t1) (substitute s t2)
  substitute  _            tcon@(TConst _) = tcon

-- Scheme has a universal quantifier for types
-- Forall a, b, c TArr (TArr "a" "b") (TVar "c")
-- ∀ a,b,c. (a -> b) -> c
data Scheme = Forall (Set Id) Type
  deriving (Eq)

instance Show Scheme where
  show (Forall s ty) = prefix ++ show ty
    where prefix = if Set.null s
                   then ""
                   else "\\-/ " ++ showList (Set.toList s) ++ ". "
          showList [] = ""
          showList (x:[]) = x
          showList (x:xs) = x ++  ", " ++ showList xs


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
  substitute :: Substitution -> Scheme -> Scheme
  substitute (Subt s) sm@(Forall is ty) =
    Forall is (substitute (Subt (s `Map.restrictKeys` (fvs sm))) ty)

-- Q: How should we describe the substitution?
-- A: Substitution is nothing but a map from id to a type.
--    It is a process of replacing type of one term with another type
--    It will be used in specializing type variables in our typechecking algorithm
newtype Substitution = Subt (Map.Map Id Type)
  deriving (Eq, Semigroup ,Monoid)

-- Support of a substitution is just its domain without things like (a ~ a)
-- supp(S) = {a | Sa ≠ a}
supp :: Substitution -> Set Id
supp (Subt s) = Set.filter (\a -> Map.lookup a s /= Just (TVar a)) ks
  where ks = Set.fromList $ Map.keys s

-- Set of involved type variables itv(S) = {a | b ∈ supp(s), a ∈ {b} U ftv(Sb)} 
itv :: Substitution -> Set Id
itv s = Set.filter (\a -> Set.member a (f a)) bs
  where
    bs = supp s
    f = \b -> Set.insert b (fvs (substitute s (TVar b)))
  
  
instance Show Substitution where
  show (Subt m) = "Subst {" ++ (foldl (\a b -> b ++ ", " ++ a) "" elems) ++ "}"
    where
    elems = fmap (\(i, t) -> "(" ++ i ++ " ~ " ++ show t ++ ")") (Map.toList m)

sub :: Id -> Type -> Substitution
sub a t = Subt (Map.singleton a t)

class Substitutable a where
  substitute :: Substitution -> a -> a

consistent :: Substitution -> Substitution -> Bool
consistent s1@(Subt m1) s2@(Subt m2) = all (\v -> composable (Map.lookup v m1)  (Map.lookup v m2)) vs  -- hyper efficient?
    where vs = Set.intersection (supp s1) (supp s2)
          composable :: Maybe Type -> Maybe Type -> Bool
          composable (Just (TConst TInt)) (Just (TConst TBool)) = False
          composable (Just (TConst TBool)) (Just (TConst TInt)) = False
          
          composable _  _ = True
          
-- This means subsitution is composable (if it is consistent obviously)
-- if  a ~ b &&  b ~ c holds
--  ==>  a ~ c holds
-- however, a ~ Bool , a ~ Int is inconsistent and hence not composable
-- a ~ b && c ~ d should return {a ~ b, c ~ d}
instance Substitutable Substitution where
  substitute :: Substitution -> Substitution -> Substitution
  substitute s@(Subt m) s'@(Subt m') =
    if consistent s s'
    then Subt ((Map.restrictKeys m (ks Set.\\ ks')) `Map.union` fmap (substitute s) m')
    else error $ "Substitution is not composable for:\n\t" ++ show s ++ "\n\t" ++ show s' 
    where ks = supp s
          ks' = supp s'
        
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
  substitute :: Substitution -> Context -> Context
  substitute s (Context c) = Context ((substitute s) <$> c)

-- extend the context by adding an (id, scheme) pair
updateContext :: Context -> Unique -> Scheme -> Context
updateContext (Context gamma) e ty = Context (Map.insert e ty gamma)
