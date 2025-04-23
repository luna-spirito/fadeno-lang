module Parser (
  OpT (..),
  Ident (..),
  BuiltinT (..),
  builtinsList,
  Quantifier (..),
  BlockT (..),
  Lambda (..),
  ExVarId (..),
  Vector' (..),
  TermT (..),
  typOf,
  rowOf,
  recordOf,
  recordGet,
  typ,
  identOfBuiltin,
  pIdent,
  pTerm',
  parse,
  parseQQ,
  parseFile,
  render,
  formatFile,
) where

import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Effect.Empty qualified as E
import Data.ByteString.Char8 (pack)
import Data.ByteString.Char8 qualified as BS
import Data.Hashable (Hashable (..))
import Data.Kind (Type)
import Data.RRBVector (Vector, findIndexR, (!?), (|>))
import FlatParse.Stateful (Parser, Pos, Result (..), anyAsciiChar, ask, byteStringOf, char, empty, eof, err, failed, getPos, local, notFollowedBy, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSatisfyAscii, skipSome, string)
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (Lift (..))
import Language.Haskell.TH.Syntax qualified as TH
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, encloseSep, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, Vector, ask, local, toList)

data OpT
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show, Eq, Ord, Lift)

data Ident = Ident !ByteString !Bool -- raw name, is operator
  deriving (Show, Eq, Ord, Generic, Lift)

instance Hashable Ident

type ParserContext = Vector Ident
type Parser' = Parser ParserContext Pos

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
identSym = satisfy \x → not $ x `elem` ("\\ \n(){}[].:|" ∷ String)

-- Returns the identifier and whether it's an operator
ident ∷ Parser' Ident
ident = token do
  rawResult ← byteStringOf (skipSome identSym)
  let (result, isOp) = case BS.uncons rawResult of
        Just ('_', rest)
          | Just (rest', '_') ← BS.unsnoc rest → (rest', True)
        _ → (rawResult, False)
  guard $ not $ BS.null result
  guard $ not $ result `elem` (["=", "in", "+", "-", "/", "*", "->", "/\\", "forall", "unpack", "fadeno", "rewrite"] ∷ [ByteString])
  pure (Ident result isOp)

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

data BuiltinT
  = U32
  | Tag
  | Row
  | Record
  | List
  | TypePlus -- Type+ 0, Type+ 1, ..., Type+ Aleph
  | Eq
  | RecordGet -- Second-class!
  | RecordKeepFields
  | RecordDropFields
  -- If -- TODO: Make Choice counterpart for Record
  deriving (Show, Eq, Lift)
builtinsList ∷ [BuiltinT]
builtinsList = [U32, Tag, Row, Record, List, TypePlus, RecordGet, RecordKeepFields, RecordDropFields]

data Quantifier = Forall | Exists deriving (Show, Eq, Lift)

data BlockT = BlockLet !Ident !(Maybe TermT) !TermT !(Lambda TermT) | BlockRewrite !TermT !TermT
  deriving (Show, Eq, Lift)

newtype Lambda a = Lambda {unLambda ∷ a}
  deriving (Show, Eq, Lift)

newtype ExVarId = ExVarId (Vector Int)
  deriving (Show, Eq, Ord)

instance Hashable ExVarId where
  hashWithSalt salt (ExVarId x) = hashWithSalt salt $ toList x

instance Lift ExVarId where
  liftTyped _ = error "unsupported"

-- Vector + Lift
newtype Vector' a = Vector' (Vector a)
  deriving (Show, Eq, Functor, Foldable, Traversable, Semigroup)

instance IsList (Vector' a) where
  type Item (Vector' a) = a
  fromList = Vector' . fromList
  toList (Vector' v) = toList v

-- Need Lift a constraint for liftTyped [a]
instance (Lift a) ⇒ Lift (Vector' a) where
  liftTyped ∷ ∀ (m ∷ Type → Type). (TH.Quote m) ⇒ Vector' a → TH.Code m (Vector' a)
  liftTyped (Vector' v) =
    [||Vector' (fromList $$(liftTyped (toList v)))||]

data TermT
  = -- Term-level

    -- | Annotations only allowed on Block.
    Block !BlockT
  | Lam !Ident !(Lambda TermT)
  | Op !TermT !OpT !TermT
  | App !TermT !TermT
  | NatLit !Word32
  | TagLit !Ident
  | Sorry !Ident !TermT
  | Var !Int
  | ListLit !(Vector' TermT)
  | RecordLit !(Vector' (TermT, TermT))
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
typOf = App $ Builtin TypePlus

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
  (`Ident` False) . \case
    U32 → "U32"
    Tag → "Tag"
    Row → "Row"
    Record → "Record"
    List → "List"
    TypePlus → "Type+"
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
sepBy with x = ((:) <$> x <*> many (with *> x)) <|> pure []

-- Syntax is *a little* ambigious. I'm very sorry.

-- Standalone '='
parseEq ∷ Parser' ()
parseEq = token $ notFollowedBy $(char '=') identSym

findVar ∷ ByteString → Parser' (Maybe (Int, Bool))
findVar name = do
  vars ← ask
  case findIndexR (\(Ident eName _) → eName == name) vars of
    Just n →
      let (Ident _ eOp) = fromMaybe (error "impossible") $ vars !? n
       in pure $ Just (n, eOp)
    Nothing → pure Nothing

-- 7
parsePrim ∷ Parser' TermT
parsePrim = token do
  prim ←
    (NatLit <$> number)
      <|> (TagLit <$> ($(char '.') *> ident))
      <|> ( do
              -- Record parsing
              token $(char '{')
              let parseField = do
                    n ← parsePrim
                    parseEq
                    v ← parseTop
                    pure (n, v)
              knownFields ← fromList <$> sepBy (token $(char '|')) parseField
              token $(char '}')
              pure (RecordLit knownFields) -- Use RecordLit for parsed fields
          )
      <|> ( do
              token $(char '[')
              elems ← fromList <$> sepBy (token $(char '|')) parseTop
              token $(char ']')
              pure (ListLit elems)
          )
      <|> (BuiltinsVar <$ (notFollowedBy $(string "fadeno") identSym))
      <|> ( Var <$> do
              -- Variable parsing
              -- TODO: { x = 4 }
              Ident iName iOp ← notFollowedBy ident parseEq
              vars ← ask
              findVar iName >>= \case
                Just (n, eOp) → case (eOp, iOp) of
                  (True, False) → empty -- TODO: this is a crutch to stop user-defined operators from crashing the parser.
                  (False, True) → err =<< getPos
                  _ → pure $ length vars - n - 1
                Nothing → err =<< getPos -- TODO: better errors, overall
          )
      <|> ( $(char '(') -- Parentheses parsing
              *> parseTop
              <* $(char ')')
          )
  -- any number of accesses after the prim
  accesses ← many $ $(char '.') *> (TagLit <$> ident)
  pure
    $ foldl'
      (flip recordGet)
      prim
      accesses

-- 6
parseApp ∷ Parser' TermT
parseApp = infxl parsePrim (pure App)

-- 5
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
              $ ((,App (Builtin TypePlus) $ NatLit 0) <$> ident)
              <|> ($(char '(') *> ((,) <$> ident <*> kind) <* $(char ')'))
          Quantification q ty ki . Lambda <$> local (|> ty) manyEntries
        manyEntries =
          someEntries <|> (token $(char '.') *> parseTy)
      someEntries
  )
    <|> ( do
            $(string "sorry/")
            n ← ident
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

-- 4
parseInfixOps ∷ Parser' TermT
parseInfixOps = infxr parseTy parseOperator'
 where
  parseOperator' ∷ Parser' (TermT → TermT → TermT)
  parseOperator' = do
    i ← ident
    vars ← ask
    case i of
      Ident opName False →
        findVar opName >>= \case
          Just (idx, True) → do
            let varIdx = length vars - idx - 1 -- De Bruijn index
            pure \a b → App (App (Var varIdx) a) b
          _ → empty -- Not a known operator in this scope
      _ → empty

-- 3
parseMath1 ∷ Parser' TermT
parseMath1 =
  infxr
    parseInfixOps
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

-- 1
parseBlock ∷ Parser' TermT
parseBlock = do
  let
    binding = do
      ty ← optional do
        token $(string "/:")
        parseMath0
      name ← ident
      parseEq
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

pBS ∷ ByteString → Doc AnsiStyle
pBS = pretty . decodeUtf8Lenient

pIdent ∷ Ident → Doc AnsiStyle
pIdent (Ident x isOp) =
  let res = pBS x
   in if isOp then "_" <> res <> "_" else res

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
        Sorry _ _ → ping
        Var _ → ping
        ListLit vs → ping *> traverse_ complexity vs
        RecordLit fields → ping *> traverse_ (\(k, v) → complexity k *> complexity v) fields
        Quantification _ _ b (Lambda c) → ping *> complexity b *> complexity c
        Pi b c → ping *> complexity b *> either (complexity . unLambda . snd) complexity c
        Union a b → complexity a *> either (complexity . unLambda . snd) complexity b
        Builtin _ → ping
        BuiltinsVar → ping
        ExVar{} → ping
        UniVar _ _ _ → ping
   in runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

-- TODO: Concise syntax for `\` and `forall`
pTerm ∷ (Int, ParserContext) → TermT → Doc AnsiStyle
pTerm (oldPrec, vars) =
  withPrec oldPrec . \case
    Lam arg x →
      ( 0
      , let sep' = case unLambda x of
              Lam _ _ → " "
              _
                | isSimple (unLambda x) → " "
                | otherwise → line
         in annotate (color Magenta) "\\"
              <> pIdent arg
              <> annotate (color Magenta) "."
              <> sep'
              <> pTerm (0, vars |> arg) (unLambda x)
      )
    block@(Block{}) →
      ( 1
      , let
          go ∷ ParserContext → TermT → ([Doc AnsiStyle], TermT, ParserContext)
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
      ( 5
      , let kind' = case kind of
              App (Builtin TypePlus) (NatLit 0) → mempty
              _ → " :" <+> pTerm (5, vars) kind
            q' = case q of
              Forall → "forall"
              Exists → "exists"
         in annotate (color Cyan) q' <+> pIdent name <> kind' <> "." <+> pTerm (5, vars |> name) (unLambda ty) -- Quantifier binder not op
      )
    Pi inTy outTy →
      ( 5
      , either (\(name, _) → pIdent name <+> ": ") mempty outTy <> pTerm (6, vars) inTy
          <+> "->"
          <+> case outTy of
            Left (name, outTy') → pTerm (5, vars |> name) $ unLambda outTy' -- Pi binder not op, use new prec 5
            Right outTy' → pTerm (5, vars) outTy' -- Use new prec 5
      )
    Union a b →
      ( 5
      , case b of
          Left (n, b') → pIdent n <+> ":" <+> pTerm (6, vars) a <+> "/\\" <+> pTerm (5, vars |> n) (unLambda b')
          Right b' → pTerm (6, vars) a <+> "/\\" <+> pTerm (5, vars) b'
      )
    Sorry x _ → (7, "sorry/" <> pIdent x)
    App (App (Builtin RecordGet) (TagLit tag)) rec →
      (7, pTerm (7, vars) rec <> "." <> pIdent tag)
    App lam arg2 → case lam of
      App (Var opIdx) arg1
        | Just (Ident opName True) ← vars !? (length vars - opIdx - 1) → -- An operator
            (4, pTerm (5, vars) arg1 <+> pBS opName <+> pTerm (4, vars) arg2)
      _ →
        -- Not an operator or out of bounds
        (6, pTerm (6, vars) lam <+> pTerm (7, vars) arg2)
    Builtin x → (7, "fadeno." <> pIdent (identOfBuiltin x))
    BuiltinsVar → (7, "fadeno")
    NatLit x → (7, pretty x)
    TagLit x → (7, "." <> pIdent x)
    RecordLit fields →
      ( 7
      , encloseSep
          (annotate (color White) "{")
          (annotate (color White) "}")
          (annotate (color White) " | ")
          (fmap (\(n, v) → pTerm (7, vars) n <+> annotate (color Cyan) "=" <+> pTerm (0, vars) v) (toList fields))
      )
    ListLit vec → (7, encloseSep "[" "]" " | " $ fmap (\x → pTerm (0, vars) x) (toList vec))
    Var x → (7, maybe ("@" <> pretty x) pIdent $ vars !? (length vars - x - 1))
    -- RecordGet a b -> case b of
    --   TagLit b' -> (6, pTerm 6 a <> "." <> pIdent b')
    --   _ -> (5, "fadeno/get" <+> pTerm 6 a <+> pTerm 6 b)
    ExVar n l t → (7, "(exi@" <> pretty (show l) <+> pIdent n <> maybe mempty (\t' → " :" <+> pTerm (0, vars) t') t <> ")")
    UniVar x' l t → (7, "(uni@" <> pretty l <+> pIdent x' <+> ":" <+> pTerm (0, vars) t <> ")")

pTerm' ∷ TermT → Doc AnsiStyle
pTerm' = pTerm (0, [])

parse ∷ ParserContext → ByteString → Either Text TermT
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
