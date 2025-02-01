module Parser where

import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Effect.Empty qualified as E
import FlatParse.Basic (Parser, Pos, Result (..), anyAsciiChar, byteStringOf, char, empty, err, failed, getPos, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSome, string, eof, notFollowedBy)
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, ask, local)
import GHC.IO.Unsafe (unsafePerformIO)

-- For now, just untyped.

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord)

data Ident = Ident !ByteString | UIdent !Int
  deriving (Show, Eq, Ord, Generic)
instance Hashable Ident

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

ident ∷ Parser' Ident
ident = token do
  result ← byteStringOf (skipSome $ satisfy \x → not $ x `elem` ("\\ \n=().:" :: String))
  guard $ not $ result `elem` ["in", "+", "-", "/", "*", "U32", "->", "forall"]
  pure $ Ident result

{-
Type Constructs of Cedille:
  ∀ X : 𝒌 . T – this is impredicative quantification over types X of kind 𝒌.
  Π x : T . T’ – this is dependent function space, where the return type T’ may mention the input argument x.
  λ X : 𝒌 . T – this is a type-level function over types X of kind 𝒌.
  λ x : T . T’ – this is a type-level function over terms x of type T.
  T t – this is applying a type-level function T to a term t.
  T · T’ – this is applying a type-level function T to a type T’ (note the required center dot).
  X – type variables are types, of course. 

See unicode shortcuts for how to type these symbols in Cedille mode.

To the above constructs, Cedille adds the following, discussed more below:

  ι x : T . T’ – dependent intersection of T and T’, where T’ may contain x.
  { t ≃ t’ } – untyped equality between terms t and t’.
  ∀ x : T . T’ – the dependent type for functions taking in an erased argument x of type T (aka implicit product) 
-}

newtype MetaVar' = MetaVar' (IORef (Either TermT Int)) deriving Eq

instance Show MetaVar' where
  show (MetaVar' x) = case unsafePerformIO $ readIORef x of
    Left t → show t
    Right n → show n

data TermT
  -- Term-level
  = Let !(NonEmpty (Ident, TermT)) !TermT
  | Lam !Ident TermT
  | Op !TermT !OpT !TermT
  | App !TermT !TermT
  | NatLit !Word32
  -- Type-level
  | Var !Ident
  | Forall !Ident !TermT !TermT -- Cedille: forall X : 𝒌 | T / Fadeno: forall X : 𝒌. T
  | U32
  | Pi !(Maybe Ident) !TermT !TermT -- Cedille: Π x : T | T’ / Fadeno: x : T -> T'
  | Ty -- ★
  | MetaVar !MetaVar' -- Actually belongs in TTermT
  -- | 
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

-- 6
parsePrim ∷ Parser' TermT
parsePrim = token $
  (U32 <$ $(string "U32"))
  <|> (Ty <$ $(string "Type"))
  <|> (NatLit <$> number)
  <|> (Var <$> notFollowedBy ident (token $ $(char '=') <|> $(char ':')))
  <|> ($(char '(')
      *> parseTop
      <* $(char ')'))

-- 5
-- Tokens???
parseApp ∷ Parser' TermT
parseApp = infxl parsePrim (pure App)

-- 4
parseTy :: Parser' TermT
parseTy =
  (do
    token $(string "forall")
    name ← ident
    kind ← (token $(char ':') *> parseTy) <|> pure Ty
    $(char '.')
    into ← parseTy
    pure $ Forall name kind into)
  <|> (do
    inName <- optional $ (ident <* $(char ':'))
    inTy <- parseApp
    token $(string "->")
    outT ← parseTy
    pure $ Pi inName inTy outT)
  <|> parseApp

parseMath1 ∷ Parser' TermT
parseMath1 =
  infxr
    parseTy
    ( operator >>= \case
        Mul → pure \x → Op x Mul
        Div → pure \x → Op x Div
        _ → empty
    )

parseMath0 ∷ Parser' TermT
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

-- parseNode :: Parser' TermT
-- parseNode = do
  -- captures ← some $ $(char '-') *> ident
  -- pos ← isJust <$> optional $(char '+')
  -- $(char '>')
  -- Node captures pos <$> parseTop

parseLet ∷ Parser' TermT
parseLet = do
  defs ← someNonEmpty do
    name ← ident
    token $ $(char '=')
    expr ← parseTop
    pure (name, expr)
  ( token do
      $(string "in")
      val ← parseTop
      pure $ Let defs val
    )

parseTop ∷ Parser' TermT
parseTop =
  token $
    -- parseNode
      {-<|>-} parseLet
      <|> (token ($(char '\\')) *> (Lam <$> ident <* $(char '.') <*> parseTop))
      <|> parseMath0
      <|> (err =<< getPos)

pIdent ∷ Ident → Doc AnsiStyle
pIdent = \case
  Ident x → pretty $ decodeUtf8Lenient x
  UIdent x → "/" <> pretty x

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

isSimple ∷ TermT → Bool
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
      NatLit _ → ping
      Var _ → ping
      Ty → ping
      Forall _ b c -> ping *> complexity b *> complexity c
      Pi _ b c -> ping *> complexity b *> complexity c
      U32 -> ping
   in
    runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

pTermT ∷ Int → TermT → Doc AnsiStyle
pTermT oldPrec =
  withPrec oldPrec . \case
    Lam arg x →
      ( 0
      , let sep = case x of
              Lam _ _ → " "
              _
                | isSimple x → " "
                | otherwise → line
         in annotate (color Magenta) "\\" <> pIdent arg <> "." <> sep <> pTermT 0 x
      )
    Let defs i →
      ( 1
      , vsep (toList defs <&> \(name, val) → pIdent name <+> annotate (color Cyan) "=" <> softline <> nest 2 (pTermT 0 val))
          <> line
          <> annotate (color Cyan) "in"
          <+> nest 2 (pTermT 1 i)
      )
    Op a op b →
      let prec = case op of
            Add → 2
            Sub → 2
            Mul → 3
            Div → 3
       in (prec, pTermT prec a <+> pOp op <+> pTermT prec b)
    Forall name kind ty -> (4,
      let
        kind' = case kind of
          Ty → mempty
          _ → " :" <+> pTermT 4 kind
      in annotate (color Cyan) "forall" <+> pIdent name <> kind' <> "." <+> pTermT 4 ty)
    Pi inName inTy outTy -> (4, maybe mempty (\x -> pIdent x <+> ": ") inName <> pTermT 5 inTy <+> "->" <+> pTermT 4 outTy)
    App lam arg → (5, pTermT 5 lam <+> pTermT 6 arg)
    Ty -> (6, "Type")
    U32 -> (6, "U32")
    NatLit x → (6, pretty x)
    Var x → (6, pIdent x)
    MetaVar (MetaVar' x) → case unsafePerformIO (readIORef x) of
      Left t → (oldPrec, pTermT oldPrec t) 
      Right i → (6, "(meta " <> pretty i <> ")")

parse ∷ ByteString → Either Text TermT
parse inp = case runParser (parseTop <* eof) inp of
  OK x "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error: uncaught failure"

parseFile ∷ FilePath → IO (Either Text TermT)
parseFile x = parse <$> readFileBinary x

parseFileOrDie ∷ FilePath → IO TermT
parseFileOrDie x = either (error . show) id <$> parseFile x

printTermT ∷ TermT → IO ()
printTermT expr = renderIO stdout $ layoutSmart defaultLayoutOptions $ pTermT 0 expr <> line
