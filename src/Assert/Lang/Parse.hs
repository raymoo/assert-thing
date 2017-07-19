module Assert.Lang.Parse ( programP
                         ) where

import Assert.Lang

import Text.Trifecta (Parser)
import qualified Text.Trifecta as P
import qualified Text.Parser.Token.Highlight as P

-- import Data.HashSet (HashSet)
import qualified Data.HashSet as HS

import Control.Applicative
import Data.Foldable (asum)

variableStyle :: P.IdentifierStyle Parser
variableStyle =
  P.IdentifierStyle { P._styleName = "variable"
                    , P._styleStart = P.letter
                    , P._styleLetter = P.alphaNum
                    , P._styleReserved = HS.fromList [ "let"
                                                     , "in"
                                                     , "if"
                                                     , "then"
                                                     , "else"
                                                     , "true"
                                                     , "false"
                                                     , "assert"
                                                     , "?"
                                                     , "="
                                                     ]
                    , P._styleHighlight = P.Identifier
                    , P._styleReservedHighlight = P.ReservedIdentifier
                    }

ident :: Parser String
ident = P.ident variableStyle

reserve :: String -> Parser ()
reserve = P.reserve variableStyle

exprP :: Parser (Expr ())
exprP = P.try binOpP <|> nonBinP

programP :: Parser (Expr ())
programP = exprP <* P.eof

nonBinP :: Parser (Expr ())
nonBinP = P.parens exprP
          <|> intP
          <|> varP
          <|> letP
          <|> unknownIntP
          <|> assertP
          <|> ifP
          <|> P.try boolP

intP :: Parser (Expr u)
intP = ConstInt <$> P.token P.integer

boolP :: Parser (Expr u)
boolP = ConstBool True <$ reserve "true"
        <|> ConstBool False <$ reserve "false"

opP :: Parser BinOp
opP = asum . map makeP $ ops
  where makeP (symbol, op) = op <$ P.symbol symbol
        ops = [ ("+" , Add)
              , ("-" , Sub)
              , ("<=", Leq)
              , ("<" , Lt)
              , (">=", Geq)
              , (">" , Gt)
              , ("==", Eq)
              , ("/=", Neq)
              , ("&&", And)
              , ("||", Or)
              ]

binOpP :: Parser (Expr ())
binOpP = BinOp <$> nonBinP <*> opP <*> nonBinP

unknownIntP :: Parser (Expr ())
unknownIntP = UnknownInt () <$ reserve "?"

varP :: Parser (Expr u)
varP = Var . Variable <$> ident

letP :: Parser (Expr ())
letP = reserve "let" *>
  (Let . Variable <$> ident <*> (P.symbol "=" *> exprP) <*> (reserve "in" *> exprP))

assertP :: Parser (Expr ())
assertP = do
  caret <- P.careting
  reserve "assert" *> (Assert caret <$> exprP)

ifP :: Parser (Expr ())
ifP = reserve "if" *> (Ite <$> exprP <*> (reserve "then" *> exprP) <*> (reserve "else" *> exprP))
