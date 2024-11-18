module Parser where

import RIO
import FlatParse.Basic (Parser, satisfyAscii, anyAsciiChar, failed, satisfy, skipMany, byteStringOf, char, string, runParser, Result (..), skipSome, empty, err, Pos, posLineCols, getPos)

-- For now, just untyped.

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord)

newtype Ident = Ident ByteString
  deriving (Show, Eq, Ord)

type Parser' = Parser Pos

space :: Parser' ()
space = skipMany (satisfyAscii (\x → x == ' ' || x == '\n'))

token :: Parser' a → Parser' a
token x = space *> x <* space

digit :: Parser' Word32
digit = anyAsciiChar >>= \case
  '0' → pure 0
  '1' → pure 1
  '2' → pure 2
  '3' → pure 3
  '4' → pure 4
  '5' → pure 5
  '6' → pure 6
  '7' → pure 7
  '8' → pure 8
  '9' → pure 9
  _ → failed

number :: Parser' Word32
number = token $ foldl' (\acc x → acc + x) 0 <$> some digit

op :: Parser' OpT
op = token $ anyAsciiChar >>= \case
  '+' → pure Add
  '-' → pure Sub
  '*' → pure Mul
  '/' → pure Div
  _ → failed

ident :: Parser' Ident
ident = token do
  result ← byteStringOf (skipSome $ satisfy \x → x /= '\\' && x /= ' ' && x /= '\n' && x /= '=' && x /= '(' && x /= ')')
  guard $ not $ result `elem` ["let", "in", "+", "-", "/", "*"]
  pure $ Ident result

data ExprT
  = Lam !Ident ExprT
  | Let ![(Ident, ExprT)] !ExprT
  | Op !ExprT !OpT !ExprT
  | App !ExprT !ExprT
  | Nat !Word32
  | Var !Ident
  deriving (Show, Eq)

infxr :: Parser' a -> Parser' (a -> a -> a) -> Parser' a
infxr a oper = do
  a' ← a
  (do
      oper' ← oper
      oper' a' <$> infxr a oper
    ) <|> pure a'

infxl :: Parser' a -> Parser' (a -> a -> a) -> Parser' a
infxl a oper = a >>= infxl' where
  infxl' prev =
    do
      oper' <- oper
      next <- a
      infxl' $ oper' prev next
    <|> pure prev

parsePrim :: Parser' ExprT
parsePrim = token $
  Nat <$> number
  <|> Var <$> ident
  <|> $(char '(') *> parseTop <* $(char ')')

parseApp :: Parser' ExprT
parseApp = infxl parsePrim (pure App)

parseMath1 :: Parser' ExprT
parseMath1 =
  infxr parseApp (op >>= \case
    Mul -> pure \x -> Op x Mul
    Div -> pure \x -> Op x Div
    _ -> empty
  )

parseMath0 :: Parser' ExprT
parseMath0 =
  infxr parseMath1 (op >>= \case
    Add -> pure \x -> Op x Add
    Sub -> pure \x -> Op x Sub
    _ -> empty
  )

parseLet :: Parser' ExprT
parseLet = token $ do
  defs ← some do
    token $ $(string "let")
    name ← ident
    token $ $(char '=')
    expr ← parseTop
    pure (name, expr)
  (token do
    $(string "in")
    val ← parseTop
    pure $ Let defs val)
  <|> (err =<< getPos)

parseTop :: Parser' ExprT
parseTop = token $ parseLet
  <|> token ($(char '\\')) *> (Lam <$> ident <*> parseTop)
  <|> parseMath0
  <|> (err =<< getPos)
  
parse :: ByteString → Either String ExprT
parse inp = case runParser parseTop inp of
  OK x "" → Right x
  Err e → Left $ "Unable to parse at " <> show (posLineCols inp [e])
  _ → Left "Internal error"

parseFile :: FilePath → IO (Either String ExprT)
parseFile x = parse <$> readFileBinary x
