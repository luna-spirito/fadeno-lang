module Parser where

import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Effect.Empty qualified as E
import Data.ByteString.Char8 (pack)
import Data.Foldable1 (foldl1')
import Data.Hashable (Hashable (..))
import Data.RRBVector (Vector, findIndexR, (!?), (|>))
import FlatParse.Stateful (Parser, Pos, Result (..), anyAsciiChar, ask, byteStringOf, char, empty, eof, err, failed, getPos, local, notFollowedBy, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSatisfyAscii, skipSome, string)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (Lift (..))
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, Vector, ask, local)

-- newtype RevList a = UnsafeRevList {unUnsafeRevList ∷ [a]} deriving (Functor, Show)

-- instance Semigroup (RevList a) where
--   UnsafeRevList a <> UnsafeRevList b = UnsafeRevList $ b <> a

-- instance Monoid (RevList a) where
--   mempty = []

-- revSnoc ∷ RevList a → a → RevList a
-- revSnoc (UnsafeRevList ls) x = UnsafeRevList $ x : ls

-- revUnsnoc ∷ RevList a → Maybe (RevList a, a)
-- revUnsnoc (UnsafeRevList x) = (\(v, l) → (UnsafeRevList l, v)) <$> uncons x

-- instance IsList (RevList a) where
--   type Item (RevList a) = a
--   fromList ls = UnsafeRevList $ reverse ls
--   toList (UnsafeRevList ls) = reverse ls

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord, Lift)

newtype Ident = Ident ByteString
  deriving (Show, Eq, Ord, Generic, Lift)

instance Hashable Ident

type Parser' = Parser (Vector Ident) Pos

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
  guard $ not $ result `elem` (["in", "+", "-", "/", "*", "->", "/\\", "forall", "unpack", "fadeno"] ∷ [ByteString])
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
  | RecordKeepFields
  | RecordDropFields
  -- If -- TODO: Make Choice counterpart for Record
  deriving (Show, Eq, Lift)
builtinsList ∷ [BuiltinT]
builtinsList = [U32, Tag, Row, Record, Type, RecordGet, RecordKeepFields, RecordDropFields]

data Quantifier = Forall | Exists deriving (Show, Eq, Lift)

data BlockT = BlockLet !Ident !(Maybe TermT) !TermT !(Lambda TermT) | BlockRewrite !TermT !TermT
  deriving (Show, Eq, Lift)

-- -- Ident is just for debugging here.
-- newtype ExVar' = ExVar' (IORef (Either PortableTermT (Ident, Int, Maybe PortableTermT))) deriving (Eq)

-- instance Show ExVar' where
--   show (ExVar' x) = case unsafePerformIO $ readIORef x of
--     Left t → show t
--     Right n → show n

-- instance Lift ExVar' where
--   liftTyped _ = error "Cannot lift ExVar"

newtype Lambda a = Lambda {unLambda ∷ a}
  deriving (Show, Eq, Lift)

newtype ExVarId = ExVarId (Vector Int)
  deriving (Show, Eq, Ord)

instance Hashable ExVarId where
  hashWithSalt salt (ExVarId x) = hashWithSalt salt $ toList x

instance Lift ExVarId where
  liftTyped _ = error "unsupported"

data TermT
  = -- Term-level

    -- | Annotations only allowed on Block.
    Block !BlockT
  | Lam !Ident !(Lambda TermT)
  | Op !TermT !OpT !TermT
  | App !TermT !TermT
  | NatLit !Word32
  | TagLit !Ident
  | Field !TermT !TermT
  | Unit
  | Sorry !Ident !TermT
  | Var !Int
  | -- Type-level
    Quantification !Quantifier !Ident !TermT !(Lambda TermT)
  | -- | Cedille: Π x : T | T’ / Fadeno: x : T -> T'
    Pi !TermT !(Either (Ident, Lambda TermT) TermT)
  | Union !TermT !(Either (Ident, Lambda TermT) TermT)
  | Builtin !BuiltinT
  | BuiltinsVar
  | ExVar !Ident !ExVarId !(Maybe TermT)
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
    RecordKeepFields → "record-keep-fields"
    RecordDropFields → "record-drop-fields"

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

sepBy ∷ Parser' () → Parser' a → Parser' [a]
sepBy sep x = ((:) <$> x <*> many (sep *> x)) <|> pure []

-- Syntax is *a little* ambigious. I'm very sorry.

-- 6
parsePrim ∷ Parser' TermT
parsePrim = token do
  prim ←
    (NatLit <$> number)
      <|> (TagLit <$> ($(char '.') *> (Ident <$> ident')))
      <|> ( do
              token $(char '{')
              let parseField = do
                    n ← parsePrim
                    token $(char '=')
                    v ← parseTop
                    pure (n, v)
              knownFields ← sepBy (token $(char '|')) parseField
              token $(char '}')
              case knownFields of
                x : xs → pure $ foldl1' (\a → Union a . Right) $ fmap (uncurry Field) (x :| xs)
                [] → pure Unit
          )
      <|> (BuiltinsVar <$ (notFollowedBy $(string "fadeno") identSym))
      <|> ( Var -- TODO: { x = 4 }
              <$> do
                i ← notFollowedBy ident $ token $(char '=')
                vars ← ask
                case findIndexR (== i) vars of
                  Just n → pure $ length vars - n - 1
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
      let
        kind = do
          token $(char ':')
          parseTy
        someEntries = do
          (ty, ki) ←
            token
              $ ((,App (Builtin Type) $ NatLit 0) <$> ident)
              <|> ($(char '(') *> ((,) <$> ident <*> kind) <* $(char ')'))
          Quantification q ty ki . Lambda <$> local (|> ty) manyEntries
        manyEntries =
          someEntries <|> (token $(char '.') *> parseTy)
      someEntries
  )
    <|> ( do
            $(string "sorry/")
            n ← Ident <$> ident'
            token $ $(char ':')
            ty ← parseTy
            pure $ Sorry n ty
        )
    <|> do
      -- Fused: parseApp <|> (->) <|> (/\)
      inNameM ← optional $ (ident <* $(char ':'))
      inTy ← parseApp
      ( ( do
            token $ $(string "->")
            outTy ← maybe (Right <$>) (\name → fmap (Left . (name,) . Lambda) . local (|> name)) inNameM parseTy
            pure $ Pi inTy outTy
        )
          <|> ( do
                  token $ $(string "/\\")
                  rightTy ← maybe (Right <$>) (\name → fmap (Left . (name,) . Lambda) . local (|> name)) inNameM parseTy
                  pure $ Union inTy rightTy
              )
          <|> ( do
                  guard $ isNothing inNameM
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

-- someNonEmpty ∷ (Alternative f) ⇒ f a → f (NonEmpty a)
-- someNonEmpty f = (:|) <$> f <*> many f

-- parseNode :: Parser' TermT
-- parseNode = do
-- captures ← some $ $(char '-') *> ident
-- pos ← isJust <$> optional $(char '+')
-- \$(char '>')
-- Node captures pos <$> parseTop

-- 1
parseBlock ∷ Parser' TermT
parseBlock = do
  let
    binding = do
      ty ← optional do
        token $(string "/:")
        parseMath0
      name ← ident
      token $(char '=')
      expr ← parseTop
      pure (name, ty, expr)
    someEntries =
      ( do
          (name, ty, expr) ← binding
          rest ← Lambda <$> (local (|> name) manyEntries)
          pure $ Block (BlockLet name ty expr rest)
      )
        <|> ( do
                token $ $(string "rewrite")
                rewrite ← parseTop
                rest ← manyEntries
                pure $ Block (BlockRewrite rewrite rest)
            )
    manyEntries =
      someEntries
        <|> ( do
                token $ $(string "in")
                parseTop
            )
  someEntries

-- 0
parseLam ∷ Parser' TermT
parseLam = token do
  $(char '\\')
  idents ← some ident
  $(char '.')
  let
    parseBod = \case
      [] → parseTop
      (x : xs) → local (|> x) $ parseBod xs
  bod ← parseBod idents
  pure $ foldr (\n → Lam n . Lambda) bod idents

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

--

pIdent ∷ Ident → Doc AnsiStyle
pIdent = \case
  Ident x → pretty $ decodeUtf8Lenient x

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
        Lam _ (Lambda x) → ping *> complexity x
        Block defs →
          ping
            *> ( case defs of
                  BlockLet _ b c x → for_ b complexity *> complexity c *> complexity (unLambda x)
                  BlockRewrite r x → ping *> complexity r *> complexity x
               )
        Op a _ c → complexity a *> complexity c
        App f a → complexity f *> complexity a
        NatLit _ → ping
        TagLit _ → ping
        Unit → pure ()
        Field a b → complexity a *> complexity b
        Sorry _ _ → ping
        Var _ → ping
        Quantification _ _ b (Lambda c) → ping *> complexity b *> complexity c
        Pi b c → ping *> complexity b *> either (complexity . unLambda . snd) complexity c
        Union a b → complexity a *> either (complexity . unLambda . snd) complexity b
        Builtin _ → ping
        BuiltinsVar → ping
        ExVar{} → ping
        -- case unsafePerformIO (readIORef x) of
        -- Left y → complexityPortable y
        -- Right _ → ping
        UniVar _ _ _ → ping
   in runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

-- TODO: Concise syntax for `\` and `forall`
pTerm ∷ (Int, Vector Ident) → TermT → Doc AnsiStyle
pTerm (oldPrec, vars) =
  withPrec oldPrec . \case
    Lam arg x →
      ( 0
      , let sep = case unLambda x of
              Lam _ _ → " "
              _
                | isSimple (unLambda x) → " "
                | otherwise → line
         in annotate (color Magenta) "\\"
              <> pIdent arg
              <> annotate (color Magenta) "."
              <> sep
              <> pTerm (0, vars |> arg) (unLambda x)
      )
    block@(Block{}) →
      ( 1
      , let
          go vars' = \case
            Block def → case def of
              BlockLet name tyM val in_ →
                let entry =
                      ( maybe mempty (\ty → "/:" <+> pTerm (2, vars') ty <> line) tyM -- TODO: split if complicated type
                          <> pIdent name
                          <+> annotate (color Cyan) "=" <> softline <> nest 2 (pTerm (0, vars') val)
                      )
                    (entries, rest, vars'') = go (vars' |> name) $ unLambda in_
                 in (entry : entries, rest, vars'')
              BlockRewrite x in_ →
                let
                  entry = "rewrite" <+> pTerm (0, vars') x
                  (entries, rest, vars'') = go vars' in_
                 in
                  (entry : entries, rest, vars'')
            r → ([], r, vars')
         in
          let (entries, rest, vars'') = go vars block
           in -- collect term = case term of
              --   Block entry →
              --     let (tEntries, tIn_) = collect next
              --      in (entry : tEntries, tIn_)
              --   _ → pure term
              -- (entries, in_) = collect block
              -- (renderedEntries, vars'') =
              --   foldl'
              --     ( \(acc, vars') → \case
              --         BlockLet name tyM val →
              --           ( ( maybe mempty (\ty → "/:" <+> pTerm (2, vars') ty <> line) tyM -- TODO: split if complicated type
              --                 <> pIdent name
              --                 <+> annotate (color Cyan) "=" <> softline <> nest 2 (pTerm (0, vars') val)
              --             )
              --               : acc
              --           , vars' |> name
              --           )
              --         BlockRewrite x → (("rewrite" <+> pTerm (0, vars') x) : acc, vars')
              --     )
              --     (mempty, vars)
              --     entries

              vsep entries
                <> line
                <> annotate (color Cyan) "in"
                <+> nest 2 (pTerm (1, vars'') rest)
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
         in annotate (color Cyan) q' <+> pIdent name <> kind' <> "." <+> pTerm (4, vars |> name) (unLambda ty)
      )
    Sorry x _ → (6, "sorry/" <> pIdent x) -- 6 and not 4 since type is not rendered
    Pi inTy outTy →
      ( 4
      , either (\(name, _) → pIdent name <+> ": ") mempty outTy <> pTerm (5, vars) inTy
          <+> "->"
          <+> case outTy of
            Left (name, outTy') → pTerm (4, vars |> name) $ unLambda outTy'
            Right outTy' → pTerm (4, vars) outTy'
      )
    Union a b →
      ( 4
      , case b of
          Left (n, b') → pIdent n <+> ":" <+> pTerm (5, vars) a <+> "/\\" <+> pTerm (6, vars) (unLambda b')
          Right b' → pTerm (5, vars) a <+> "/\\" <+> pTerm (6, vars) b'
      )
    App (App (Builtin RecordGet) (TagLit tag)) rec →
      (6, pTerm (6, vars) rec <> "." <> pIdent tag)
    App lam arg → (5, pTerm (5, vars) lam <+> pTerm (6, vars) arg)
    Builtin x → (6, "fadeno." <> pIdent (identOfBuiltin x)) -- TODO: use record parser
    BuiltinsVar → (6, "fadeno")
    NatLit x → (6, pretty x)
    TagLit x → (6, "." <> pIdent x)
    Field name val → (6, "{" <+> pTerm (6, vars) name <+> "=" <+> pTerm (6, vars) val <+> "}")
    -- Field name val →
    --   ( 6
    --   , let
    --       -- (vars', Fields knownFields rest) = case fields of
    --       --   Left (Lambda a) → (vars |> Ident "self", a)
    --       --   Right a → (vars, a)
    --       field (n, v) = pTerm (6, vars) n <+> "=" <+> pTerm (0, vars) v
    --       -- TODO: separator other than " " if not isSimple.
    --       renderRest = case rest of
    --         Nothing → mempty
    --         Just rest' → "|| " <> pTerm (2, vars') rest' <> " "
    --       renderFields = \case
    --         [] → mempty
    --         [x] → " " <> field x <> " "
    --         x : xs → " " <> field x <> " |" <> renderFields xs
    --       (braceS, braceE) = case fields of
    --         Left _ → ("(", ")")
    --         Right _ → (mempty, mempty)
    --      in
    --       "{" <> braceS <> renderFields knownFields <> renderRest <> braceE <> "}"
    --   )
    Unit → (6, "{}")
    Var x → (6, maybe ("@" <> pretty x) pIdent $ vars !? (length vars - x - 1))
    -- RecordGet a b -> case b of
    --   TagLit b' -> (6, pTerm 6 a <> "." <> pIdent b')
    --   _ -> (5, "fadeno/get" <+> pTerm 6 a <+> pTerm 6 b)
    ExVar n l t → (6, "(exi@" <> pretty (show l) <+> pIdent n <> maybe mempty (\t' → " :" <+> pTerm (0, vars) t') t <> ")")
    -- case unsafePerformIO (readIORef x) of
    -- Left t → (oldPrec, pTerm (oldPrec, vars) $ unport t $ length vars)
    -- Right (n, l, t) → (6, "(exi@" <> pretty l <+> pIdent n <> maybe mempty (\t' → " :" <+> pTerm (0, vars) (unport t' $ length vars)) t <> ")")
    UniVar x' l t → (6, "(uni@" <> pretty l <+> pIdent x' <+> ":" <+> pTerm (0, vars) t <> ")")

pTerm' ∷ TermT → Doc AnsiStyle
pTerm' = pTerm (0, [])

parse ∷ Vector Ident → ByteString → Either Text TermT
parse vars inp = case runParser (parseTop <* eof) vars 0 inp of
  OK x _ "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error: uncaught failure"

parseQQ ∷ Vector Ident → QuasiQuoter
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
formatFile = render . pTerm' <=< parseFile
