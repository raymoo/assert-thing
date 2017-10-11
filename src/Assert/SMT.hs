{-# LANGUAGE DataKinds, MultiWayIf, TupleSections #-}
module Assert.SMT ( checkExpr
                  , Check(..)
                  , SMTM
                  , Command
                  ) where

import Assert.Lang

import SimpleSMT (Solver, SExpr)
import qualified SimpleSMT as SMT

import Data.Functor.Foldable

import Text.Trifecta.Rendering (Caret)

import Control.Monad.Trans.RWS.Strict

import Control.Monad (void, join)
import Data.Foldable (for_, traverse_)
import Data.Maybe (catMaybes)

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (a, c) = (f a, c)

newtype Fresh a = Fresh { unFresh :: (Int -> (Int, a)) }

instance Functor Fresh where
  fmap f (Fresh g) = Fresh ((fmap.fmap) f g)

instance Applicative Fresh where
  pure a = Fresh $ \i -> (i, a)
  Fresh f <*> Fresh g = Fresh $ \i ->
    let (i', a) = f i
    in a <$> g i'

fresh :: Fresh Int
fresh = Fresh $ \i -> (i + 1, i)

renumberExpr :: Expr u -> (Int, Expr Int)
renumberExpr e = unFresh (traverse (const fresh) e) $ 0

makeIdent :: String -> Int -> String
makeIdent s 0 = s
makeIdent s n = s ++ "-" ++ show n

addUnknowns :: Solver -> Int -> IO [String]
addUnknowns solver n = do
  for_ names $ \name ->
    SMT.declare solver name SMT.tInt
  pure names
  where names = map (makeIdent "?") [0 .. n - 1]

opType :: BinOp -> SExpr
opType op =
  case compileBinOp op of
    IntOp _  -> SMT.tInt
    CompOp _ -> SMT.tBool
    BoolOp _ -> SMT.tBool

data Command = Declare Variable SExpr
             | Define Variable SExpr SExpr
             | Assume SExpr
  deriving (Show)

runCommand :: Solver -> Command -> IO ()
runCommand solver (Declare (Variable s) e) = void $ SMT.declare solver s e
runCommand solver (Define (Variable s) varType varDef) = void $ SMT.define solver s varType varDef
runCommand solver (Assume e) = SMT.assert solver e

-- | Difflist of commands to run before checkSat
data Check = Check ([Command] -> [Command]) Caret

check :: Solver -> [String] -> Check -> IO (Maybe [(String, SMT.Value)])
check solver names (Check f _) = do
  SMT.push solver
  traverse_ (runCommand solver) commands
  checkRes <- SMT.check solver
  result <- case (names, checkRes) of
              ([], SMT.Sat)       -> pure (Just [])
              (_,  SMT.Sat) -> Just <$> SMT.getConsts solver names
              _             -> pure Nothing
  SMT.pop solver
  pure result
  where commands = f []

data SMTFun =
  SMTFun Variable Int (Env SMTBinding, SMT.SExpr) [Variable] (Expr Int)
  -- ^ Name, remaining calls (to limit recursion), environment, arguments, body
  deriving (Show)

data SMTBinding =
  VarBinding SExpr Variable
  | FunctionBinding SMTFun
  deriving (Show)

data SMTValue =
  -- type, expression
  SExprValue SExpr SExpr
  | FunctionValue SMTFun
  deriving (Show)

bindingToValue :: SMTBinding -> SMTValue
bindingToValue (VarBinding t (Variable varName)) = SExprValue t (SMT.Atom varName)
bindingToValue (FunctionBinding fun) = FunctionValue fun

-- | Read environment is (Binding environment, logical context)
-- State is (Unique var number, reversed list of global commands)
type SMTM a =
  RWS (Env SMTBinding, SMT.SExpr) [Check] (Env Int, [Command]) a

-- | Applies a function inside the Check constructor
mapCheck :: (([Command] -> [Command]) -> ([Command] -> [Command]))
         -> Check -> Check
mapCheck f (Check g r) = Check (f g) r

uniqueVar :: Variable -> SMTM Variable
uniqueVar v@(Variable vName) = state go
  where go (env, fEnv) = let (newEnv, i) = updateEnv 0 (+1) v env
                         in (Variable $ makeIdent vName i, (newEnv, fEnv))

outputGlobalCommand :: Command -> SMTM ()
outputGlobalCommand comm = modify modState
  where modState (env, commList) = (env, comm : commList)

withCondition :: SExpr -> SMTM a -> SMTM a
withCondition cond = censor (map addCondition) . local addContext
  where addCondition = mapCheck ((Assume cond :) .)
        addContext = fmap (SMT.and cond)

withBinding :: Variable -> SMTBinding -> SMTM a -> SMTM a
withBinding var binding action =
  local (mapFst (bindEnv var binding)) action

withVar :: Variable -> SExpr -> SExpr -> SMTM a -> SMTM a
withVar var varType varDef action = do
  -- Variable as represented in SMT queries
  smtVar <- uniqueVar var
  outputGlobalCommand $ Define smtVar varType varDef
  withBinding var (VarBinding varType smtVar) action

withFun :: Variable -> Int -> [Variable] -> Expr Int -> SMTM a -> SMTM a
withFun fName recsLeft args body action = do
  curEnv <- ask

  let smtFun = SMTFun fName recsLeft curEnv args body
  withBinding fName (FunctionBinding smtFun) action

believe :: SMT.SExpr -> SMTM ()
believe p = do
  (_, context) <- ask
  outputGlobalCommand . Assume $ context `SMT.implies` p

getVar :: Variable -> SMTM SMTBinding
getVar var = asks (\(env, _) -> lookupEnvU env var)

applyFun :: Variable -> [SMTValue] -> SMTM (Maybe SMTValue)
applyFun v args = do
  FunctionBinding (SMTFun fName recsLeft funEnv params body) <- getVar v
  if
    | length args /= length params ->
      error "applyFun: Bad function argument count"
    | recsLeft <= 0 -> do
      believe $ SMT.bool False
      pure Nothing
    | otherwise ->
        local (const funEnv)
        . withAll params
        -- Make the function available to call recursively
        . withFun fName (recsLeft - 1) params body
        $ cata checkExprF body
  where bindOne param val = case val of
          SExprValue t e -> withVar param t e
          FunctionValue fun -> withBinding param (FunctionBinding fun)
        withAll params = foldr (.) id $ zipWith bindOne params args

checkExpr :: Expr u -> IO [([(String, SMT.Value)], Caret)]
checkExpr e = do
  solver <- SMT.newSolver "z3" ["-smt2","-in"] =<< Just <$> SMT.newLogger 0
  unknownNames <- addUnknowns solver unknownCount
  let initEnv = (emptyEnv, SMT.bool True)
      (_, (_, globalComms), checks) =
        runRWS (cata checkExprF eNumbered) initEnv (emptyEnv, [])
      checkOne c@(Check _ r) = (fmap.fmap) (, r) . check solver unknownNames $ c
  traverse_ (runCommand solver) (reverse globalComms)
  assgnsList <- traverse checkOne checks
  pure $ catMaybes assgnsList
  where (unknownCount, eNumbered) = renumberExpr e

applyOp :: BinOp -> SExpr -> SExpr -> SExpr
applyOp Add = SMT.add
applyOp Sub = SMT.sub
applyOp Lt  = SMT.lt
applyOp Leq = SMT.leq
applyOp Gt  = SMT.gt
applyOp Geq = SMT.geq
applyOp Eq  = SMT.eq
applyOp Neq = (SMT.not .) . SMT.eq
applyOp And = SMT.and
applyOp Or  = SMT.or

checkExprF :: ExprF Int (SMTM (Maybe SMTValue))
           -> SMTM (Maybe SMTValue)
checkExprF (ConstIntF x)  = (pure.pure) (SExprValue SMT.tInt (SMT.int x))
checkExprF (ConstBoolF p) = (pure.pure) (SExprValue SMT.tBool (SMT.bool p))
checkExprF (BinOpF ev1 op ev2) = do
  mRes1 <- ev1
  mRes2 <- ev2
  pure $ combine <$> mRes1 <*> mRes2
  where combine (SExprValue _ e1) (SExprValue _ e2) =
          SExprValue (opType op) (applyOp op e1 e2)
        combine _                  _                  = error "Function in binop"

checkExprF (UnknownIntF u) =
  pure . Just $ SExprValue SMT.tInt (SMT.Atom . makeIdent "?" . fromIntegral $ u)
checkExprF (VarF v) = do
  Just . bindingToValue <$> getVar v
checkExprF (LetF v ev1 ev2) = do
  mRes1 <- ev1
  case mRes1 of
    Nothing -> pure Nothing
    Just (SExprValue t1 e1) -> withVar v t1 e1 ev2
    Just (FunctionValue fun) -> withBinding v (FunctionBinding fun) ev1
checkExprF (AssertF r ev) = do
  mRes <- ev
  case mRes of
    Nothing -> pure Nothing
    Just (SExprValue _ e) -> do
      tell $ [Check (Assume (SMT.not e) :) r]
      (pure.pure) (SExprValue SMT.tInt (SMT.int 0))
    _ -> error "Tried to assert a function"
checkExprF (BelieveF ev1) = do
  mRes1 <- ev1
  case mRes1 of
    Nothing -> pure ()
    Just (SExprValue _ e) -> believe e
    _                     -> error "Tried to believe a function"
  pure Nothing
checkExprF (IteF ev1 ev2 ev3) = do
  mRes1 <- ev1
  case mRes1 of
    Nothing -> pure Nothing
    Just (SExprValue _ e1) -> do
      mRes2 <- withCondition e1 ev2
      mRes3 <- withCondition (SMT.not e1) ev3
      merge e1 mRes2 mRes3
    Just _ -> error "Function used as condition"
  where merge e1 (Just (SExprValue t2 e2)) (Just (SExprValue _  e3)) =
          (pure.pure) (SExprValue t2 (SMT.ite e1 e2 e3))
        merge _ (Just a) Nothing         = (pure.pure) a
        merge _ Nothing         (Just a) = (pure.pure) a
        merge _ Nothing         Nothing  = pure Nothing
        merge _ _               _        = error "Function result in condition body"
checkExprF (LetFunF fName args body inner) = withFun fName recLimit args body inner
  where recLimit = 3
checkExprF (AppF fName argEvs) = do
  mArgs <- sequence <$> sequence argEvs
  fmap join . traverse (applyFun fName) $ mArgs
