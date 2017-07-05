{-# LANGUAGE DataKinds #-}
module Assert.SMT ( checkExpr
                  ) where

import Assert.Lang

import SimpleSMT (Solver, SExpr)
import qualified SimpleSMT as SMT

import Data.Functor.Foldable

import Control.Applicative
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
  case compileBinOp op of
    IntOp _  -> SMT.tInt
    CompOp _ -> SMT.tBool
    BoolOp _ -> SMT.tBool

checkExpr :: Expr u -> IO (Maybe [(String, SMT.Value)])
checkExpr e = do
  solver <- SMT.newSolver "z3" ["-smt2","-in"] =<< Just <$> SMT.newLogger 0
  unknownNames <- addUnknowns solver unknownCount
  eResult <- snd . cata (checkExprF solver unknownNames) eFinal $ emptyEnv
  pure $
    case eResult of
      Left assgns -> Just assgns
      _           -> Nothing
  where (unknownCount, eNumbered) = renumberExpr e
        eFinal = uniquifyExpr eNumbered

check :: Solver -> [String] -> IO (Maybe [(String, SMT.Value)])
check solver names = do
  checkRes <- SMT.check solver
  case (names, checkRes) of
    ([], SMT.Sat)       -> pure (Just [])
    (_,  SMT.Sat) -> Just <$> SMT.getConsts solver names
    _             -> pure Nothing

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

checkExprF :: Solver
           -> [String]
           -> ExprF Int (Env SExpr -> (SExpr, IO (Either [(String, SMT.Value)] SExpr)))
           -> Env SExpr
           -> (SExpr, IO (Either [(String, SMT.Value)] SExpr))
checkExprF _ _ (ConstIntF x)     _   = (SMT.tInt, puree (SMT.int x))
checkExprF _ _ (ConstBoolF p)    _   = (SMT.tBool, puree (SMT.bool p))
checkExprF _ _ (BinOpF ev1 op ev2) env = (opType op, applyOp op <<$>> e1 <<*>> e2)
  where (_, e1) = ev1 env
        (_, e2) = ev2 env
checkExprF _ _ (UnknownIntF u)   _   =
  (SMT.tInt, puree . SMT.Atom . makeIdent "?" . fromIntegral $ u)
checkExprF _ _ (VarF v@(Variable varName)) env = (lookupEnvU env v, puree . SMT.Atom $ varName)
checkExprF solver _ (LetF v@(Variable varName) ev1 ev2) env = (t2, action)
  where (t1, e1) = ev1 env
        (t2, e2) = ev2 (bindEnv v t1 env)
        action = do
          eVarDef <- e1
          case eVarDef of
            Left assgns -> pure (Left assgns)
            Right varDef -> do
              _ <- SMT.define solver varName t1 varDef
              e2
checkExprF solver names (AssertF ev) env = (SMT.tInt, action)
  where action = do
          eExpr <- snd (ev env)
          case eExpr of
            Left assgns -> pure (Left assgns)
            Right expr -> do
              SMT.push solver
              SMT.assert solver (SMT.not expr)
              mAssgns <- check solver names
              SMT.pop solver
              pure $ maybeToLeft mAssgns (SMT.int 0)
checkExprF solver _ (IteF ev1 ev2 ev3) env = (t2, action)
  where (_,  e1) = ev1 env
        (t2, e2) = ev2 env
        (_,  e3) = ev3 env
        action = do
          eCond <- e1
          case eCond of
            Left assgns -> pure . Left $  assgns
            Right cond -> do
              -- Then clause: condition is true
              SMT.push solver
              SMT.assert solver cond
              eThen <- e2
              SMT.pop solver

              -- Else clause: condition is false
              SMT.push solver
              SMT.assert solver (SMT.not cond)
              eElse <- e3
              SMT.pop solver

              pure $ SMT.ite cond <$> eThen <*> eElse
        

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

