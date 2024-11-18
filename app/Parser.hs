module Parser where

import RIO hiding (many, some, bracket, try)
import Text.Megaparsec (Parsec, single, some, satisfy, token, takeWhile1P, runParser, label, try)
import Lexer (TokenT(..), Ident(..), OpT(..), lex)
import Prelude hiding (lex)
import Text.Megaparsec.Error (ParseErrorBundle)

data ExprT
  = Lam !Ident ExprT
  | Let ![(Ident, ExprT)] !ExprT
  | Op !ExprT !OpT !ExprT
  | App !ExprT !ExprT
  | Nat !Word32
  | Var !Ident
  deriving (Show, Eq)

type Parser = Parsec () [TokenT]

ident :: Parser Ident
ident = token
  (\case
    TokenIdent x → Just x
    _ → Nothing)
  mempty

single_ :: TokenT → Parser ()
single_ = void . single

parsePrim :: Parser ExprT
parsePrim = label "Prim" $
  let
    bracket opening = satisfy
      (\case
        TokenBracket opening2
          | opening == opening2 → True
        _ → False
      )
    nat = token (\case
      TokenNat x → Just x
      _ → Nothing) mempty
    var = token (\case
        TokenIdent x → Just x
        _ → Nothing
      ) mempty
  in Nat <$> nat
  <|> Var <$> var
  <|> bracket True *> parseTop <* bracket False
  
parseApp :: Parser ExprT
parseApp = label "app" $ -- LEFT-ASSOCIATIVE
  try (App <$> parsePrim <*> parseApp)
  <|> parsePrim

parseMath1 :: Parser ExprT
parseMath1 = label "math1" $
  let math1Op =
        token (\case
          TokenOp Mul → Just Mul
          TokenOp Div → Just Div
          _ → Nothing
        ) mempty
  in try (Op <$> parseApp <*> math1Op <*> parseMath1)
  <|> parseApp

parseMath0 :: Parser ExprT
parseMath0 = label "math0" $
  let math0Op =
        token (\case
          TokenOp Add → Just Add
          TokenOp Sub → Just Sub
          _ → Nothing
        ) mempty
  in try (Op <$> parseMath1 <*> math0Op <*> parseMath0)
  <|> parseMath1

parseLet :: Parser ExprT
parseLet = label "Let" do
  defs ← some do
    single_ TokenLet
    name ← ident
    single_ TokenAssign
    expr ← parseTop
    pure (name, expr)
  single_ TokenIn
  val ← parseTop
  pure $ Let defs val

parseTop :: Parser ExprT
parseTop = label "Top" $
  parseLet
  <|> single_ TokenLam *> (Lam <$> ident <*> parseTop)
  <|> parseMath0

type ParseErr = Maybe (ParseErrorBundle [TokenT] ())

parseText :: ByteString → Either ParseErr ExprT
parseText inp = maybe (Left Nothing) (either (Left . Just) Right . runParser parseTop "<inline>") $ lex inp

parseFile :: FilePath → IO (Either ParseErr ExprT)
parseFile x = parseText <$> readFileBinary x
