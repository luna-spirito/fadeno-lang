module Lexer where

import RIO
import FlatParse.Basic (Parser, satisfyAscii, anyAsciiChar, failed, satisfy, skipMany, byteStringOf, char, string, runParser, Result (OK), skipSome)

-- For now, just untyped.

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord)

newtype Ident = Ident ByteString
  deriving (Show, Eq, Ord)

type Parser' = Parser ()

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
number = foldl' (\acc x → acc + x) 0 <$> some digit

op :: Parser' OpT
op = anyAsciiChar >>= \case
  '+' → pure Add
  '-' → pure Sub
  '*' → pure Mul
  '/' → pure Div
  _ → failed

ident :: Parser' Ident
ident = do
  result ← byteStringOf (skipSome $ satisfy \x → x /= '\\' && x /= ' ' && x /= '\n' && x /= '=' && x /= '(' && x /= ')')
  guard $ result /= "let" && result /= "in"
  pure $ Ident result

space :: Parser' ()
space = skipMany (satisfyAscii (\x → x == ' ' || x == '\n'))

data TokenT
  = TokenOp !OpT
  | TokenNat !Word32
  | TokenLam
  | TokenLet
  | TokenAssign
  | TokenIn
  | TokenIdent !Ident
  | TokenBracket !Bool -- opening?
  deriving (Show, Eq, Ord)

tokens :: Parser' TokenT
tokens = space *> (
  TokenOp <$> op
  <|> TokenNat <$> number
  <|> TokenLam <$ $(char '\\')
  <|> TokenLet <$ $(string "let")
  <|> TokenIn <$ $(string "in")
  <|> TokenAssign <$ $(char '=')
  <|> TokenIdent <$> ident
  <|> TokenBracket True <$ $(char '(')
  <|> TokenBracket False <$ $(char ')'))

lex :: ByteString → Maybe [TokenT]
lex = runParser (many tokens <* space) >>> \case
  OK x _ → Just x -- TODO: ""
  _ → Nothing
