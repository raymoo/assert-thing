{-# LANGUAGE DataKinds #-}
module Assert.SMT ( checkExpr
                  ) where

import Assert.Lang

import SimpleSMT (Solver, SExpr)
import qualified SimpleSMT as SMT

import Data.Functor.Foldable

import Data.Foldable (for_)

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
uniquifyExprF (AssertF ev) bindings freshes = Assert <$> ev bindings freshes
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
  case op of
    Add -> SMT.tInt
    Sub -> SMT.tInt
    Leq -> SMT.tBool
    Eq  -> SMT.tBool
    And -> SMT.tBool
    Or  -> SMT.tBool

checkExpr :: Expr u -> IO (Maybe [(String, SMT.Value)])
checkExpr e = do
  solver <- SMT.newSolver "z3" ["-smt2","-in"] =<< Just <$> SMT.newLogger 0
  unknownNames <- addUnknowns solver unknownCount
  _ <- snd . cata (checkExprF solver) eFinal $ emptyEnv
  checkRes <- SMT.check solver
  case (unknownNames, checkRes) of
    ([], SMT.Sat)       -> pure (Just [])
    (_,  SMT.Sat) -> Just <$> SMT.getConsts solver unknownNames
    _             -> pure Nothing
  where (unknownCount, eNumbered) = renumberExpr e
        eFinal = uniquifyExpr eNumbered

applyOp :: BinOp -> SExpr -> SExpr -> SExpr
applyOp Add = SMT.add
applyOp Sub = SMT.sub
applyOp Leq = SMT.leq
applyOp Eq  = SMT.eq
applyOp And = SMT.and
applyOp Or  = SMT.or

checkExprF :: Solver
           -> ExprF Int (Env SExpr -> (SExpr, IO SExpr))
           -> Env SExpr
           -> (SExpr, IO SExpr)
checkExprF _ (ConstIntF x)     _   = (SMT.tInt, pure (SMT.int x))
checkExprF _ (ConstBoolF p)    _   = (SMT.tBool, pure (SMT.bool p))
checkExprF _ (BinOpF ev1 op ev2) env = (opType op, applyOp op <$> e1 <*> e2)
  where (_, e1) = ev1 env
        (_, e2) = ev2 env
checkExprF _ (UnknownIntF u)   _   =
  (SMT.tInt, pure . SMT.Atom . makeIdent "?" . fromIntegral $ u)
checkExprF _ (VarF v@(Variable varName)) env = (lookupEnvU env v, pure . SMT.Atom $ varName)
checkExprF solver (LetF v@(Variable varName) ev1 ev2) env = (t2, action)
  where (t1, e1) = ev1 env
        (t2, e2) = ev2 (bindEnv v t1 env)
        action = do
          varDef <- e1
          _ <- SMT.define solver varName t1 varDef
          e2
checkExprF solver (AssertF ev) env = (SMT.tInt, action)
  where action = do
          expr <- snd (ev env)
          SMT.assert solver (SMT.not expr)
          pure (SMT.int 0)
checkExprF _ (IteF ev1 ev2 ev3) env = (t2, SMT.ite <$> e1 <*> e2 <*> e3)
  where (_,  e1) = ev1 env
        (t2, e2) = ev2 env
        (_,  e3) = ev3 env
