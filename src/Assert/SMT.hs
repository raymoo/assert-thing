{-# LANGUAGE DataKinds, TupleSections #-}
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
import qualified Text.Trifecta.Rendering as R

import Control.Monad.Trans.RWS.Strict

import Control.Applicative
import Control.Monad (void)
import Data.Foldable (for_)
import Data.Maybe (catMaybes)

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

uniqueVar :: Variable -> Env Int -> (Env Int, Variable)
uniqueVar v@(Variable vName) env = (newEnv, Variable $ makeIdent vName i)
  where (newEnv, i) = updateEnv 0 (+1) v env

-- The first environment keeps track of the next fresh name for each variable
-- The second environment keeps track of the unique name in scope for each variable
uniquifyExprF :: ExprF u (Env Variable -> Env Int -> (Env Int, Expr u))
              -> Env Variable
              -> Env Int
              -> (Env Int, Expr u)
uniquifyExprF (ConstIntF x) _ freshes = (freshes, ConstInt x)
uniquifyExprF (ConstBoolF p) _ freshes = (freshes, ConstBool p)
uniquifyExprF (BinOpF ev1 op ev2) bindings freshes =
  let (freshes',  e1) = ev1 bindings freshes
      (freshes'', e2) = ev2 bindings freshes'
  in (freshes'', BinOp e1 op e2)
uniquifyExprF (UnknownIntF u) _ freshes = (freshes, UnknownInt u)
uniquifyExprF (VarF var) bindings freshes = (freshes, Var $ lookupEnvU bindings var)
uniquifyExprF (LetF var ev1 ev2) bindings freshes =
  let (freshes', e1) = ev1 bindings freshes
      (freshes'', newVar) = uniqueVar var freshes'
      bindings' = bindEnv var newVar bindings
      (freshes''', e2) = ev2 bindings' freshes''
  in (freshes''', Let newVar e1 e2)
uniquifyExprF (AssertF r ev) bindings freshes = Assert r <$> ev bindings freshes
uniquifyExprF (IteF ev1 ev2 ev3) bindings freshes =
  let (freshes', e1) = ev1 bindings freshes
      (freshes'', e2) = ev2 bindings freshes'
      (freshes''', e3) = ev3 bindings freshes''
  in (freshes''', Ite e1 e2 e3)

uniquifyExpr :: Expr u -> Expr u
uniquifyExpr e = snd (cata uniquifyExprF e emptyEnv emptyEnv)

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
check solver names (Check f r) = do
  SMT.push solver
  traverse (runCommand solver) commands
  checkRes <- SMT.check solver
  result <- case (names, checkRes) of
              ([], SMT.Sat)       -> pure (Just [])
              (_,  SMT.Sat) -> Just <$> SMT.getConsts solver names
              _             -> pure Nothing
  SMT.pop solver
  pure result
  where commands = f []

type SMTM a = RWS (Env SExpr) [Check] () a

-- | Applies a functoin inside the Check constructor
mapCheck :: (([Command] -> [Command]) -> ([Command] -> [Command]))
         -> Check -> Check
mapCheck f (Check g r) = Check (f g) r

withCondition :: SExpr -> SMTM a -> SMTM a
withCondition cond = censor (map addCondition)
  where addCondition = mapCheck ((Assume cond :) .)

withVar :: Variable -> SExpr -> SExpr -> SMTM a -> SMTM a
withVar var varType varDef = censor (map addDef) . local addVar
  where addDef = mapCheck ((Define var varType varDef :) .)
        addVar env = bindEnv var varType env

getVarType :: Variable -> SMTM SExpr
getVarType var = asks (\env -> lookupEnvU env var)

checkExpr :: Expr u -> IO [([(String, SMT.Value)], Caret)]
checkExpr e = do
  solver <- SMT.newSolver "z3" ["-smt2","-in"] Nothing
  unknownNames <- addUnknowns solver unknownCount
  let (_, checks) = evalRWS (cata checkExprF eFinal) emptyEnv ()
      checkOne c@(Check _ r) = (fmap.fmap) (, r) . check solver unknownNames $ c
  assgnsList <- traverse checkOne checks
  pure $ catMaybes assgnsList
  where (unknownCount, eNumbered) = renumberExpr e
        eFinal = uniquifyExpr eNumbered

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

checkExprF :: ExprF Int (SMTM (SExpr, SExpr))
           -> SMTM (SExpr, SExpr)
checkExprF (ConstIntF x)  = pure (SMT.tInt, SMT.int x)
checkExprF (ConstBoolF p) = pure (SMT.tBool, SMT.bool p)
checkExprF (BinOpF ev1 op ev2) = do
  (_, e1) <- ev1
  (_, e2) <- ev2
  pure (opType op, applyOp op e1 e2)
checkExprF (UnknownIntF u) =
  pure (SMT.tInt, SMT.Atom . makeIdent "?" . fromIntegral $ u)
checkExprF (VarF v@(Variable varName)) = do
  t <- getVarType v
  pure (t, SMT.Atom varName)
checkExprF (LetF v@(Variable varName) ev1 ev2) = do
  (t1, e1) <- ev1
  withVar v t1 e1 ev2
checkExprF (AssertF r ev) = do
  (_, e) <- ev
  tell $ [Check (Assume (SMT.not e) :) r]
  pure (SMT.tInt, SMT.int 0)
checkExprF (IteF ev1 ev2 ev3) = do
  (_,  e1) <- ev1
  (t2, e2) <- withCondition e1 ev2
  (_,  e3) <- withCondition (SMT.not e1) ev3
  pure (t2, SMT.ite e1 e2 e3)

maybeToLeft :: Maybe a -> b -> Either a b
maybeToLeft (Just a) _ = Left a
maybeToLeft Nothing b  = Right b

puree :: (Applicative f, Applicative g) => a -> f (g a)
puree = pure . pure

(<<$>>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<<$>>) = fmap . fmap
infixl 4 <<$>>

(<<*>>) :: (Applicative f, Applicative g) => f (g (a -> b)) -> f (g a) -> f (g b)
(<<*>>) = liftA2 (<*>)
infixl 4 <<*>>

