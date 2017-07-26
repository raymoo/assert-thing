{-# LANGUAGE DeriveTraversable, GeneralizedNewtypeDeriving, TypeFamilies #-}
module Assert.Lang ( Expr(..)
                   , ExprF(..)
                   , BinOp(..)
                   , CompiledBinOp(..)
                   , compileBinOp
                   , Variable(..)
                   , Env
                   , emptyEnv
                   , listToEnv
                   , lookupEnv
                   , lookupEnvU
                   , bindEnv
                   , updateEnv
                   , askValues
                   , eval
                   ) where

import Data.Functor.Foldable

import Text.Trifecta.Rendering (Caret)

import Data.Hashable

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.Maybe (fromMaybe)

data Expr u = ConstInt Integer
            | ConstBool Bool
            | BinOp (Expr u) BinOp (Expr u)
            | UnknownInt u
            | Var Variable
            | Let Variable (Expr u) (Expr u)
            | Assert Caret (Expr u)
            | Ite (Expr u) (Expr u) (Expr u)
            | LetFun Variable [Variable] (Expr u) (Expr u)
            | App Variable [Expr u]
  deriving (Show, Functor, Foldable, Traversable)

data ExprF u a = ConstIntF Integer
               | ConstBoolF Bool
               | BinOpF a BinOp a
               | UnknownIntF u
               | VarF Variable
               | LetF Variable a a
               | AssertF Caret a
               | IteF a a a
               | LetFunF Variable [Variable] (Expr u) a
               | AppF Variable [a]
  deriving (Show, Functor)

type instance Base (Expr u) = ExprF u

instance Recursive (Expr u) where
  project (ConstInt n)     = ConstIntF n
  project (ConstBool p)    = ConstBoolF p
  project (BinOp op e1 e2) = BinOpF op e1 e2
  project (UnknownInt u)   = UnknownIntF u
  project (Var v)          = VarF v
  project (Let v e1 e2)    = LetF v e1 e2
  project (Assert c e)     = AssertF c e
  project (Ite e1 e2 e3)   = IteF e1 e2 e3
  project (LetFun v vs body inner)  = LetFunF v vs body inner
  project (App f args)     = AppF f args

data BinOp = Add
           | Sub
           | Lt
           | Leq
           | Gt
           | Geq
           | Eq
           | Neq
           | And
           | Or
  deriving (Show)

data CompiledBinOp = IntOp (Integer -> Integer -> Integer)
                   | BoolOp (Bool -> Bool -> Bool)
                   | CompOp (Integer -> Integer -> Bool)

compileBinOp :: BinOp -> CompiledBinOp
compileBinOp Add = IntOp (+)
compileBinOp Sub = IntOp (-)
compileBinOp Lt  = CompOp (<)
compileBinOp Leq = CompOp (<=)
compileBinOp Gt  = CompOp (>)
compileBinOp Geq = CompOp (>=)
compileBinOp Eq  = CompOp (==)
compileBinOp Neq = CompOp (/=)
compileBinOp And = BoolOp (&&)
compileBinOp Or  = BoolOp (||)

newtype Variable = Variable String
  deriving (Eq, Show, Hashable)

data Value = IntVal Integer
           | BoolVal Bool
  deriving (Show, Eq)

newtype Env a = Env (HashMap Variable a)
  deriving (Show)

emptyEnv :: Env a
emptyEnv = Env HM.empty

lookupEnv :: Env a -> Variable -> Maybe a
lookupEnv (Env m) v = HM.lookup v m

-- Unsafe version
lookupEnvU :: Show a => Env a -> Variable -> a
lookupEnvU env v@(Variable vName) =
  fromMaybe (error $ "Unbound variable: " ++ vName) (lookupEnv env v)

bindEnv :: Variable -> a -> Env a -> Env a
bindEnv v a (Env m) = Env (HM.insert v a m)

listToEnv :: [(Variable, a)] -> Env a
listToEnv = Env . HM.fromList

updateEnv :: a -> (a -> a) -> Variable -> Env a -> (Env a, a)
updateEnv def f v env = (bindEnv v result env, result)
  where result = maybe def f . lookupEnv env $ v

-- | Fills in all unknowns using the provided action
askValues :: Applicative t => t Integer -> Expr u -> t (Expr Integer)
askValues action = traverse (const action)

evalOne :: ExprF Integer (Env Value -> Value) -> Env Value -> Value
evalOne (ConstIntF n)        _   = IntVal n
evalOne (ConstBoolF p)       _   = BoolVal p
evalOne (BinOpF ev1 bop ev2) env =
  case (compileBinOp bop, ev1 env, ev2 env) of
    (IntOp  op, IntVal  x, IntVal  y) -> IntVal (op x y)
    (CompOp op, IntVal  x, IntVal  y) -> BoolVal (op x y)
    (BoolOp op, BoolVal p, BoolVal q) -> BoolVal (op p q)
    _                                 -> error "evalOne: type mismatch"
evalOne (UnknownIntF u)     _   = IntVal u
evalOne (VarF v)            env = lookupEnvU env v
evalOne (LetF v ev1 ev2)    env = ev2 innerEnv
  where innerEnv = bindEnv v (ev1 env) env
evalOne (AssertF _ _)         _   = IntVal 0
evalOne (IteF ev1 ev2 ev3)  env =
  case ev1 env of
    BoolVal True  -> ev2 env
    BoolVal False -> ev3 env
    _             -> error "evalOne: type mismatch"
evalOne _ _ = error "evalOne: Not all expressions supported"

eval :: Expr Integer -> Value
eval e = cata evalOne e emptyEnv
