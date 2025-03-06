module Parser where

import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Effect.Empty qualified as E
import Data.ByteString.Char8 (pack)
import FlatParse.Stateful (Parser, Pos, Result (..), anyAsciiChar, byteStringOf, char, empty, eof, err, failed, getPos, notFollowedBy, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSatisfyAscii, skipSome, string, ask, local)
import GHC.IO.Unsafe (unsafePerformIO)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (Lift (..))
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, ask, local)
import RIO.List (elemIndex)
import qualified RIO.List.Partial as P

-- For now, just untyped.

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord, Lift)

data Ident = Ident !ByteString | UIdent !Int
  deriving (Show, Eq, Ord, Generic, Lift)

instance Hashable Ident

type Parser' = Parser [Ident] Pos

space ∷ Parser' ()
space =
  skipMany
    $ skipSatisfyAscii (\x → x == ' ' || x == '\n')
    <|> ($(string "//") *> skipMany (satisfyAscii (/= '\n')))

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
number = token $ foldl' (\acc x → acc * 10 + x) 0 <$> some digit

operator ∷ Parser' OpT
operator =
  token
    $ anyAsciiChar
    >>= \case
      '+' → pure Add
      '-' → pure Sub
      '*' → pure Mul
      '/' → pure Div
      _ → failed

-- TODO: block words from ident' as well?.. probably not.
-- TODO: Convert blocklists to functions
identSym ∷ Parser' Char
identSym = satisfy \x → not $ x `elem` ("\\ \n=(){}[].:|" ∷ String)

ident' ∷ Parser' ByteString
ident' = byteStringOf (skipSome identSym)

ident ∷ Parser' Ident
ident = token do
  result ← ident'
  guard $ not $ result `elem` (["in", "+", "-", "/", "*", "->", "forall", "unpack", "fadeno"] ∷ [ByteString])
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

-- TODO: Unpack

data BuiltinT
  = U32
  | Tag
  | Row
  | Record
  | Type -- Type+ 0, Type+ 1, ..., Type+ Aleph
  | Eq
  | RecordGet -- Second-class!
  -- If -- TODO: Make Choice counterpart for Record
  deriving (Show, Eq, Lift)
builtinsList ∷ [BuiltinT]
builtinsList = [U32, Tag, Row, Record, Type, RecordGet]

data Quantifier = Forall | Exists deriving (Show, Eq, Lift)

data Fields = FRow | FRecord deriving (Show, Eq, Lift)

data BlockT = BlockLet !Ident !(Maybe TermT) !TermT | BlockRewrite !TermT
  deriving (Show, Eq, Lift)

-- Ident is just for debugging here.
newtype ExVar' = ExVar' (IORef (Either TermT (Ident, (Int, Maybe TermT)))) deriving (Eq)

instance Show ExVar' where
  show (ExVar' x) = case unsafePerformIO $ readIORef x of
    Left t → show t
    Right n → show n

instance Lift ExVar' where
  liftTyped _ = error "Cannot lift ExVar"

data TermT
  = -- Term-level

    -- | Annotations only allowed on Block.
    Block !BlockT !TermT
  | Lam !Ident TermT
  | Op !TermT !OpT !TermT
  | App !TermT !TermT
  | NatLit !Word32
  | TagLit !Ident
  | FieldsLit !Fields ![(TermT, TermT)] !(Maybe TermT) -- TODO: remove list?
  | Sorry !Ident !TermT
  | Var !Int
  | -- Type-level
    Quantification !Quantifier !Ident !TermT !TermT
  | -- | Cedille: Π x : T | T’ / Fadeno: x : T -> T'
    Pi !(Maybe Ident) !TermT !TermT
  | Builtin !BuiltinT
  | BuiltinsVar
  | ExVar !ExVar'
  | UniVar !Ident !Int !TermT
  deriving (Show, Eq, Lift)

typOf ∷ TermT → TermT
typOf = App $ Builtin Type

rowOf ∷ TermT → TermT
rowOf = App $ Builtin Row

recordOf ∷ TermT → TermT
recordOf = App $ Builtin Record

recordGet ∷ TermT → TermT → TermT
recordGet tag record = (Builtin RecordGet `App` tag) `App` record

typ ∷ TermT
typ = typOf $ NatLit 0

identOfBuiltin ∷ BuiltinT → Ident
identOfBuiltin =
  Ident . \case
    U32 → "U32"
    Tag → "Tag"
    Row → "Row"
    Record → "Record"
    Type → "Type+"
    Eq → "Eq"
    RecordGet → "record-get"

-- If → "if"

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

-- Syntax is *a little* ambigious. I'm very sorry.

-- 6
parsePrim ∷ Parser' TermT
parsePrim = token do
  prim ←
    (NatLit <$> number)
      <|> (TagLit <$> ($(char '.') *> (Ident <$> ident')))
      <|> ( do
              token $ $(char '{')
              let parseField = do
                    n ← parsePrim
                    fields ← token $ ($(char '=') $> FRecord) <|> ($(char ':') $> FRow)
                    v ← parseTop
                    pure ((n, v), fields)
                  parseMany = do
                    (x, fields1) ← parseField
                    let
                      after = case fields1 of
                        FRecord → id
                        FRow → local (Ident "self":)
                      more = after
                        ((do
                          token $(char '|')
                          (res, fields2) ← parseField
                          guard $ fields1 == fields2
                          (res:) <$> more
                        ) <|> (pure []))
                    xs ← after more
                    pure (fields1, x:xs)
                  parseEmpty = do
                    fields ← token $ ($(char ':') $> FRow) <|> pure FRecord
                    pure (fields, [])
              (fields, knownFields) ← parseMany <|> parseEmpty
              rest ← optional do
                token $ $(string "||")
                parseMath0
              space *> $(char '}')
              pure $ FieldsLit fields knownFields rest
          )
      <|> (BuiltinsVar <$ (notFollowedBy $(string "fadeno") identSym))
      <|> (Var <$>
        do
          i ← notFollowedBy ident $ token $(char '=')
          vars ← ask
          case elemIndex i vars of
            Just n → pure n
            Nothing → err =<< getPos -- TODO: better errors, overall
        )
      <|> ( $(char '(')
              *> parseTop
              <* $(char ')')
          )
  -- any number of accesses after the prim
  accesses ← many $ $(char '.') *> (TagLit . Ident <$> ident')
  pure
    $ foldl'
      (flip recordGet)
      prim
      accesses

-- 5
-- Tokens???
parseApp ∷ Parser' TermT
parseApp = infxl parsePrim (pure App)

-- 4
parseTy ∷ Parser' TermT
parseTy =
  ( do
      q ← token $ ($(string "forall") $> Forall) <|> ($(string "exists") $> Exists)
      -- TODO: unify syntax with how Pi works?
      let kind = do
            token $(char ':')
            parseTy
          manyEntry =
            token
              $ ((,App (Builtin Type) $ NatLit 0) <$> ident)
              <|> ($(char '(') *> ((,) <$> ident <*> kind) <* $(char ')'))
      binds ←
        (some manyEntry <* token $(char '.'))
          <|> (((\a b → [(a, b)]) <$> ident <*> kind) <* token $(char '.'))
      into ← parseTy
      pure $ foldr (uncurry $ Quantification q) into binds
  )
    <|> ( do
            $(string "sorry/")
            n ← Ident <$> ident'
            token $ $(char ':')
            ty ← parseTy
            pure $ Sorry n ty
        )
    <|> do
      -- Fused: parseApp <|> (->)
      inName ← optional $ (ident <* $(char ':'))
      inTy ← parseApp
      ( ( do
            token $ $(string "->")
            outT ← parseTy
            pure $ Pi inName inTy outT
        )
          <|> ( do
                  guard $ isNothing inName
                  pure inTy
              )
        )

-- 3
parseMath1 ∷ Parser' TermT
parseMath1 =
  infxr
    parseTy
    ( operator >>= \case
        Mul → pure \x → Op x Mul
        Div → pure \x → Op x Div
        _ → empty
    )

-- 2
parseMath0 ∷ Parser' TermT
parseMath0 =
  infxr
    parseMath1
    ( operator >>= \case
        Add → pure \x → Op x Add
        Sub → pure \x → Op x Sub
        _ → empty
    )

someNonEmpty ∷ (Alternative f) ⇒ f a → f (NonEmpty a)
someNonEmpty f = (:|) <$> f <*> many f

-- parseNode :: Parser' TermT
-- parseNode = do
-- captures ← some $ $(char '-') *> ident
-- pos ← isJust <$> optional $(char '+')
-- \$(char '>')
-- Node captures pos <$> parseTop

-- 1
parseBlock ∷ Parser' TermT
parseBlock = do
  defs ←
    someNonEmpty
      $ ( do
            ty ← optional do
              token $(string "/:")
              parseMath0
            name ← ident
            token $(char '=')
            expr ← parseTop
            pure $ BlockLet name ty expr
        )
      <|> ( do
              token $ $(string "rewrite")
              BlockRewrite <$> parseTop
          )
  ( token do
      $(string "in")
      val ← parseTop
      pure $ foldr Block val defs
    )

-- 0
parseLam ∷ Parser' TermT
parseLam = token do
  $(char '\\')
  idents ← some ident
  $(char '.')
  let
    parseBod = \case
      [] → parseTop
      (x:xs) → local (x:) $ parseBod xs
  bod ← parseBod idents
  pure $ foldr Lam bod idents

-- 0
parseTop ∷ Parser' TermT
parseTop =
  token
    $
    -- parseNode
    {-<|>-} parseBlock
    <|> parseLam
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

-- Impure!
isSimple ∷ TermT → Bool
isSimple =
  let ping = do
        modify @Int (+ 1)
        curr ← get
        if complexThreshold curr
          then E.empty
          else pure ()
      complexity = \case
        Lam _ x → ping *> complexity x
        Block defs x →
          ping
            *> ( case defs of
                  BlockLet _ b c → for_ b complexity *> complexity c
                  BlockRewrite r → ping *> complexity r
               )
            *> complexity x
        Op a _ c → complexity a *> complexity c
        App f a → complexity f *> complexity a
        NatLit _ → ping
        TagLit _ → ping
        FieldsLit _ x y →
          for_ x (\(a, b) → complexity a *> complexity b) *> for_ y complexity
        -- RecordGet a _ -> ping *> complexity a
        Sorry _ _ → ping
        Var _ → ping
        Quantification _ _ b c → ping *> complexity b *> complexity c
        Pi _ b c → ping *> complexity b *> complexity c
        Builtin _ → ping
        BuiltinsVar → ping
        ExVar (ExVar' x) → case unsafePerformIO (readIORef x) of
          Left y → complexity y
          Right _ → ping
        UniVar _ _ c → ping *> complexity c
   in runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

-- TODO: Concise syntax for `\` and `forall`
pTerm ∷ (Int, [Ident]) → TermT → Doc AnsiStyle
pTerm (oldPrec, vars) =
  withPrec oldPrec . \case
    Lam arg x →
      ( 0
      , let sep = case x of
              Lam _ _ → " "
              _
                | isSimple x → " "
                | otherwise → line
         in annotate (color Magenta) "\\"
              <> pIdent arg
              <> annotate (color Magenta) "."
              <> sep
              <> pTerm (0, arg:vars) x
      )
    block@(Block{}) →
      ( 1
      , let
          collect term = case term of
            Block entry next →
              let (tEntries, tIn_) = collect next
               in (entry : tEntries, tIn_)
            _ → pure term
          (entries, in_) = collect block
         in
          vsep
            ( entries <&> \case
                BlockLet name tyM val →
                  maybe mempty (\ty → "/:" <+> pTerm (2, vars) ty <> line) tyM -- TODO: split if complicated type
                    <> pIdent name
                    <+> annotate (color Cyan) "=" <> softline <> nest 2 (pTerm (0, vars) val)
                BlockRewrite x → "rewrite" <+> pTerm (0, vars) x
            )
            <> line
            <> annotate (color Cyan) "in"
            <+> nest 2 (pTerm (1, vars) in_)
      )
    Op a op b →
      let prec = case op of
            Add → 2
            Sub → 2
            Mul → 3
            Div → 3
       in (prec, pTerm (prec, vars) a <+> pOp op <+> pTerm (prec, vars) b)
    Quantification q name kind ty →
      ( 4
      , let kind' = case kind of
              App (Builtin Type) (NatLit 0) → mempty
              _ → " :" <+> pTerm (4, vars) kind
            q' = case q of
              Forall → "forall"
              Exists → "exists"
         in annotate (color Cyan) q' <+> pIdent name <> kind' <> "." <+> pTerm (4, vars) ty
      )
    Sorry x _ → (6, "sorry/" <> pIdent x) -- 6 and not 4 since type is not rendered
    Pi inName inTy outTy → (4, maybe mempty (\x → pIdent x <+> ": ") inName <> pTerm (5, vars) inTy <+> "->" <+> pTerm (4, vars) outTy)
    -- Ty x -> (4, "Type/" <+> pTerm 6 x)
    App lam arg → (5, pTerm (5, vars) lam <+> pTerm (6, vars) arg)
    -- Row x → (5, "Row" <+> pTerm 6 x)
    -- Record x → (5, "Record" <+> pTerm 6 x)
    -- U32 -> (6, "U32")
    -- Tag → (6, "Tag")
    Builtin x → (6, "fadeno." <> pIdent (identOfBuiltin x)) -- TODO: use record parser
    BuiltinsVar → (6, "fadeno")
    NatLit x → (6, pretty x)
    TagLit x → (6, "." <> pIdent x)
    record@(FieldsLit fields _ _) →
      ( 6
      , let (knownFields, rest) =
              let f tail' = case tail' of
                    ExVar (ExVar' x)
                      | Left t ← unsafePerformIO (readIORef x) → f t
                    FieldsLit fields'' head'' tail''
                      | fields == fields'' → first (head'' <>) $ maybe ([], Nothing) f tail''
                    _ → ([], Just tail')
               in f record
            sep = case fields of
              FRecord → "="
              FRow → ":"
            field vars' (n, v) = pTerm (6, vars') n <+> sep <+> pTerm (0, vars') v
            -- TODO: separator other than " " if not isSimple.
            renderRest vars' = case rest of
              Nothing → mempty
              Just rest' → "|| " <> pTerm (2, vars') rest' <> " "
            renderFields vars' = \case
              [] → case fields of
                FRecord → renderRest vars'
                FRow → ":" <> renderRest vars'
              [x] → " " <> field vars' x <> " " <> renderRest vars'
              x : xs → " " <> field vars' x <> " |" <> renderFields
                (case fields of
                  FRecord → vars'
                  FRow → Ident "self":vars')
                xs
         in "{" <> renderFields vars knownFields <> "}"
      )
    Var x → (6, pIdent $ vars P.!! x)
    -- RecordGet a b -> case b of
    --   TagLit b' -> (6, pTerm 6 a <> "." <> pIdent b')
    --   _ -> (5, "fadeno/get" <+> pTerm 6 a <+> pTerm 6 b)
    ExVar (ExVar' x) → case unsafePerformIO (readIORef x) of
      Left t → (oldPrec, pTerm (oldPrec, vars) t)
      Right (n, (i, t)) → (6, "(exi" <+> pIdent n <+> "of" <+> pretty i <> maybe mempty (\t' → " :" <+> pTerm (0, vars) t') t <> ")")
    UniVar x' y t → (6, "(uni" <+> pIdent x' <+> "of" <+> pretty y <+> ":" <+> pTerm (0, vars) t <> ")")

pTerm' :: TermT → Doc AnsiStyle
pTerm' = pTerm (0, [])

parse ∷ [Ident] → ByteString → Either Text TermT
parse vars inp = case runParser (parseTop <* eof) vars 0 inp of
  OK x _ "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error: uncaught failure"

parseQQ ∷ [Ident] → QuasiQuoter
parseQQ vars =
  QuasiQuoter
    { quoteExp = \s → case parse vars (pack s) of
        Right t → ⟦t⟧
        Left e → fail $ "Failed to parse: " ++ show e
    , quotePat = error "No pattern support"
    , quoteType = error "No type support"
    , quoteDec = error "No declaration support"
    }

parseFile ∷ FilePath → IO TermT
parseFile x = either (error . show) id . parse [] <$> readFileBinary x

render ∷ Doc AnsiStyle → IO ()
render x = renderIO stdout $ layoutSmart defaultLayoutOptions $ x <> line

formatFile ∷ FilePath → IO ()
formatFile = render . pTerm (0, []) <=< parseFile
