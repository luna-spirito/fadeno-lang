module Parser where

import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Effect.Empty qualified as E
import FlatParse.Basic (Parser, Pos, Result (..), anyAsciiChar, byteStringOf, char, empty, err, failed, getPos, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSome, string)
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, ask, local)

-- For now, just untyped.

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord)

newtype Ident = Ident {unIdent ∷ ByteString}
  deriving (Show, Eq, Ord, Hashable)

type Parser' = Parser Pos

space ∷ Parser' ()
space = skipMany (satisfyAscii (\x → x == ' ' || x == '\n'))

token ∷ Parser' a → Parser' a
token x = space *> x <* space

digit ∷ Parser' Word32
digit =
  anyAsciiChar >>= \case
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

number ∷ Parser' Word32
number = token $ foldl' (\acc x → acc*10 + x) 0 <$> some digit

operator ∷ Parser' OpT
operator =
  token $
    anyAsciiChar >>= \case
      '+' → pure Add
      '-' → pure Sub
      '*' → pure Mul
      '/' → pure Div
      _ → failed

{-
Reserved symbols:
<space> ( ) { } [ ] \\ \n ,
Reserved keywords/operators:
+ - / * (-ident)*+?> let in
-}

ident ∷ Parser' Ident
ident = token do
  result ← byteStringOf (skipSome $ satisfy \x → not $ x `elem` ['\\', ' ', '\n', '=', '(', ')'])
  guard $ not $ result `elem` ["let", "in", "+", "-", "/", "*"]
  pure $ Ident result

data ExprT
  =
  Node ![Ident] !Bool !ExprT
  | Let !(NonEmpty (Ident, ExprT)) !ExprT
  | Lam !Ident ExprT
  | Op !ExprT !OpT !ExprT
  | App !ExprT !ExprT
  | Nat !Word32
  | Var !Ident
  | BuiltinsChurch
  deriving (Show, Eq)

infxr ∷ Parser' a → Parser' (a → a → a) → Parser' a
infxr a oper = do
  a' ← a
  ( do
      oper' ← oper
      oper' a' <$> infxr a oper
    )
    <|> pure a'

infxl ∷ Parser' a → Parser' (a → a → a) → Parser' a
infxl a oper = a >>= infxl'
 where
  infxl' prev =
    ( do
        oper' ← oper
        next ← a
        infxl' $ oper' prev next
    )
      <|> pure prev

parsePrim ∷ Parser' ExprT
parsePrim =
  token $
    BuiltinsChurch
      <$ $(string "builtins/church")
        <|> Nat
      <$> number
        <|> Var
      <$> ident
        <|> $(char '(')
      *> parseTop
      <* $(char ')')

parseApp ∷ Parser' ExprT
parseApp = infxl parsePrim (pure App)

parseMath1 ∷ Parser' ExprT
parseMath1 =
  infxr
    parseApp
    ( operator >>= \case
        Mul → pure \x → Op x Mul
        Div → pure \x → Op x Div
        _ → empty
    )

parseMath0 ∷ Parser' ExprT
parseMath0 =
  infxr
    parseMath1
    ( operator >>= \case
        Add → pure \x → Op x Add
        Sub → pure \x → Op x Sub
        _ → empty
    )

someNonEmpty :: Alternative f ⇒ f a → f (NonEmpty a)
someNonEmpty f = (:|) <$> f <*> many f

parseNode :: Parser' ExprT
parseNode = do
  captures ← some $ $(char '-') *> ident
  pos ← isJust <$> optional $(char '+')
  $(char '>')
  Node captures pos <$> parseTop

parseLet ∷ Parser' ExprT
parseLet = do
  defs ← someNonEmpty do
    token $ $(string "let")
    name ← ident
    token $ $(char '=')
    expr ← parseTop
    pure (name, expr)
  ( token do
      $(string "in")
      val ← parseTop
      pure $ Let defs val
    )

parseTop ∷ Parser' ExprT
parseTop =
  token $
    parseNode
      <|> parseLet
      <|> (token ($(char '\\')) *> (Lam <$> ident <*> parseTop))
      <|> parseMath0
      <|> (err =<< getPos)

pIdent ∷ Ident → Doc AnsiStyle
pIdent (Ident x) = pretty $ decodeUtf8Lenient x

pOp ∷ OpT → Doc AnsiStyle
pOp = \case
  Add → "+"
  Sub → "-"
  Mul → "*"
  Div → "/"

-- Left/right?
withPrec ∷ Int → (Int, Doc ann) → Doc ann
withPrec oldPrec (newPrec, bod) =
  if oldPrec > newPrec
    then "(" <> bod <> ")"
    else bod

complexThreshold ∷ Int → Bool
complexThreshold = (>= 5)

isSimple ∷ ExprT → Bool
isSimple =
  let
    ping = do
      modify @Int (+ 1)
      curr ← get
      if complexThreshold curr
        then E.empty
        else pure ()
    complexity = \case
      Lam _ x → ping *> complexity x
      Let defs x → ping *> for defs (complexity . snd) *> complexity x
      Op a _ c → complexity a *> complexity c
      App f a → complexity f *> complexity a
      Nat _ → ping
      Var _ → ping
      BuiltinsChurch → ping
   in
    runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

pExpr ∷ Int → ExprT → Doc AnsiStyle
pExpr oldPrec =
  withPrec oldPrec . \case
    Lam arg x →
      ( 0
      , let sep = case x of
              Lam _ _ → " "
              _
                | isSimple x → " "
                | otherwise → line
         in annotate (color Magenta) "\\" <> pIdent arg <> sep <> pExpr 0 x
      )
    Let defs i →
      ( 1
      , vsep (toList defs <&> \(name, val) → annotate (color Cyan) "let" <+> pIdent name <+> annotate (color Cyan) "=" <> softline <> nest 2 (pExpr 0 val))
          <> line
          <> annotate (color Cyan) "in"
          <+> nest 2 (pExpr 1 i)
      )
    Op a op b →
      let prec = case op of
            Add → 2
            Sub → 2
            Mul → 3
            Div → 3
       in (prec, pExpr prec a <+> pOp op <+> pExpr prec b)
    App lam arg → (4, pExpr 4 lam <+> pExpr 5 arg)
    Nat x → (5, pretty x)
    Var x → (5, pIdent x)
    BuiltinsChurch → (6, "builtins/church")

parse ∷ ByteString → Either Text ExprT
parse inp = case runParser parseTop inp of
  OK x "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error"

parseFile ∷ FilePath → IO (Either Text ExprT)
parseFile x = parse <$> readFileBinary x

parseFileOrDie ∷ FilePath → IO ExprT
parseFileOrDie x = fromRight (error "parsing failed") <$> parseFile x

printExpr ∷ ExprT → IO ()
printExpr expr = renderIO stdout $ layoutSmart defaultLayoutOptions $ pExpr 0 expr <> line
