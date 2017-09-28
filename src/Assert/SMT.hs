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

mapFst :: (a -> b) -> (a, d, c) -> (b, d, c)
mapFst f (a, d, b) = (f a, d, b)

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
  SMTFun Variable Int (Env (SExpr, Variable), Env SMTFun, SMT.SExpr) [Variable] (Expr Int)
  -- ^ Name, remaining calls (to limit recursion), environment, arguments, body
  deriving (Show)

-- | Read environment is (SMT type, variable name in solver, logical context)
-- State is (Unique var number, reversed list of global commands)
type SMTM a =
  RWS (Env (SExpr, Variable), Env SMTFun, SMT.SExpr) [Check] (Env Int, [Command]) a

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
        addContext (typeEnv, varEnv, context) =
          (typeEnv, varEnv, SMT.and cond context)

withVar :: Variable -> SExpr -> SExpr -> SMTM a -> SMTM a
withVar var varType varDef action = do
  -- Variable as represented in SMT queries
  smtVar <- uniqueVar var
  outputGlobalCommand $ Define smtVar varType varDef

  let addVar env = bindEnv var (varType, smtVar) env
  local (mapFst addVar) $ action

withFun :: Variable -> Int -> [Variable] -> Expr Int -> SMTM a -> SMTM a
withFun fName recsLeft args body action = do
  curEnv <- ask

  let smtFun = SMTFun fName recsLeft curEnv args body
      addFun env = bindEnv fName smtFun env

  local (\(a, b, c) -> (a, addFun b, c)) action

believe :: SMT.SExpr -> SMTM ()
believe p = do
  (_, _, context) <- ask
  outputGlobalCommand . Assume $ context `SMT.implies` p

-- | (SMT type, SMT variable)
getVar :: Variable -> SMTM (SExpr, Variable)
getVar var = asks (\(env, _, _) -> lookupEnvU env var)

getFun :: Variable -> SMTM SMTFun
getFun var = asks (\(_, env, _) -> lookupEnvU env var)

applyFun :: Variable -> [(SExpr, SExpr)] -> SMTM (Maybe (SExpr, SExpr))
applyFun v args = do
  SMTFun fName recsLeft funEnv params body <- getFun v
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
  where bindOne param (argT, argE) = withVar param argT argE
        withAll params = foldr (.) id $ zipWith bindOne params args

checkExpr :: Expr u -> IO [([(String, SMT.Value)], Caret)]
checkExpr e = do
  solver <- SMT.newSolver "z3" ["-smt2","-in"] =<< Just <$> SMT.newLogger 0
  unknownNames <- addUnknowns solver unknownCount
  let initEnv = (emptyEnv, emptyEnv, SMT.bool True)
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

checkExprF :: ExprF Int (SMTM (Maybe (SExpr, SExpr)))
           -> SMTM (Maybe (SExpr, SExpr))
checkExprF (ConstIntF x)  = (pure.pure) (SMT.tInt, SMT.int x)
checkExprF (ConstBoolF p) = (pure.pure) (SMT.tBool, SMT.bool p)
checkExprF (BinOpF ev1 op ev2) = do
  mRes1 <- ev1
  mRes2 <- ev2
  pure . fmap (opType op,) $ applyOp op <$> fmap snd mRes1 <*> fmap snd mRes2
checkExprF (UnknownIntF u) =
  pure . Just $ (SMT.tInt, SMT.Atom . makeIdent "?" . fromIntegral $ u)
checkExprF (VarF v) = do
  (t, (Variable smtVarName)) <- getVar v
  (pure.pure) (t, SMT.Atom smtVarName)
checkExprF (LetF v ev1 ev2) = do
  mRes1 <- ev1
  case mRes1 of
    Nothing -> pure Nothing
    Just (t1, e1) -> do
      withVar v t1 e1 ev2
checkExprF (AssertF r ev) = do
  mRes <- ev
  case mRes of
    Nothing -> pure Nothing
    Just (_, e) -> do
      tell $ [Check (Assume (SMT.not e) :) r]
      (pure.pure) (SMT.tInt, SMT.int 0)
checkExprF (BelieveF ev1) = do
  mRes1 <- ev1
  case mRes1 of
    Nothing -> pure ()
    Just (_, e) -> believe e
  pure Nothing
checkExprF (IteF ev1 ev2 ev3) = do
  mRes1 <- ev1
  case mRes1 of
    Nothing -> pure Nothing
    Just (_, e1) -> do
      mRes2 <- withCondition e1 ev2
      mRes3 <- withCondition (SMT.not e1) ev3
      merge e1 mRes2 mRes3
  where merge e1 (Just (t2, e2)) (Just (_,  e3)) = (pure.pure) (t2, SMT.ite e1 e2 e3)
        merge _ (Just (t2, e2)) Nothing         = (pure.pure) (t2, e2)
        merge _ Nothing         (Just (t3, e3)) = (pure.pure) (t3, e3)
        merge _ _               _               = pure Nothing
checkExprF (LetFunF fName args body inner) = withFun fName recLimit args body inner
  where recLimit = 3
checkExprF (AppF fName argEvs) = do
  mArgs <- sequence <$> sequence argEvs
  fmap join . traverse (applyFun fName) $ mArgs
