-- GHC 9.12 spends minutes optimising this module otherwise
{-# OPTIONS_GHC -O0 #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use join" #-}
module Parser (
  Bits (..),
  BlockF (..),
  BuiltinT (..),
  FieldsK (..),
  Ident (..),
  IsErased (..),
  Lambda (..),
  Module (..),
  NumDesc (..),
  ParserContext (..),
  RefineK (..),
  Quant (..),
  Term (..),
  TermF (..),
  Vector' (..),
  builtinsList,
  dotvar,
  eqOf,
  formatFile,
  formatModule,
  freshIdent,
  identOfBuiltin,
  intercept,
  loadModule,
  loadModule',
  nested,
  nestedBy',
  nestedByP,
  nestedByP',
  maxOf,
  parseQQ,
  pIdent,
  pQuant,
  pTerm,
  parse,
  parseFile,
  parseSource,
  recordGet,
  render,
  rowOf,
  typ,
  typOf,
  traverseTermF,
  pattern Op2,
) where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Lift (sendIO)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (State, StateC, evalState, execState, get, modify, runState)
import Control.Carrier.Writer.Church (Writer, censor, listen)
import Control.Effect.Empty qualified as E
import Control.Effect.Reader qualified as R
import Data.ByteString.Char8 qualified as BS
import Data.Functor.Classes (Eq1, Ord1)
import Data.Kind (Type)
import Data.RRBVector (Vector, findIndexR, zip, (!?), (|>))
import FlatParse.Stateful (Parser, Pos, Result (..), anyAsciiChar, ask, byteStringOf, char, empty, eof, err, failed, getPos, local, notFollowedBy, posLineCols, runParser, satisfyAscii, skipMany, skipSatisfy, skipSatisfyAscii, skipSome, string, try)
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (Lift (..))
import Language.Haskell.TH.Syntax qualified as TH
import NameGen qualified as N
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, encloseSep, hcat, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, Vector, ask, local, runReader, toList, try, zip)
import RIO.HashMap qualified as HM
import System.File.OsPath (readFile')
import System.OsPath (OsPath, encodeUtf, takeDirectory, unsafeEncodeUtf, (</>))

-- TODO ASAP: assocativity for operators. YeAh, TuRns oUT wE NeEd iT, wHo coUlD hAvE GuESseD?
-- (6 - 4 - 2 ≠ 6 - (4 - 2))
-- TODO: Recolour everything.

-- censor + listen
intercept ∷ ∀ w m sig a. (Has (Writer w) sig m, Monoid w) ⇒ m a → m (w, a)
intercept = censor @w (const mempty) . listen @w

data Ident = Ident !ByteString !Bool -- raw name, is operator
  deriving (Show, Eq, Ord, Generic, Lift)
instance Hashable Ident

data Quant = QEra | QNorm
  deriving (Show, Eq, Ord, Lift)

data Bits = Bits8 | Bits16 | Bits32 | Bits64
  deriving (Show, Eq, Ord, Lift)
data NumDesc = NumFin !Bool {- ≥ 0 -} !Bits | NumInf
  deriving (Show, Eq, Ord, Lift)

data BuiltinT
  = Tag
  | RowPlus
  | List
  | Bool
  | TypePlus -- Type^ 0, Type^ 1, ..., Type^ Aleph
  | Eq
  | Refl
  | RecordGet -- Second-class!
  | RecordKeepFields
  | RecordDropFields
  | ListLength
  | ListIndexL
  | Fix'
  | If -- TODO: Make Choice counterpart for Record
  | IntGte0
  | IntEq
  | TagEq
  | W
  | Wrap
  | Unwrap
  | Never
  | Any'
  | Num !NumDesc
  | Add !NumDesc
  | Mul !NumDesc
  | IntNeg !NumDesc
  deriving (Show, Eq, Ord, Lift)

builtinsList ∷ Vector BuiltinT
builtinsList =
  [Tag, RowPlus, List, Bool, TypePlus, Eq, Refl, RecordGet, RecordKeepFields, RecordDropFields, ListLength, ListIndexL, Fix', If, IntGte0, IntEq, TagEq, W, Wrap, Unwrap, Never, Any']
    <> (Num <$> nd)
    <> (Add <$> nd)
    <> (Mul <$> nd)
    <> (IntNeg <$> nd)
 where
  nd = (NumFin <$> [False, True] <*> [Bits8, Bits16, Bits32, Bits64]) <> [NumInf]

identOfBuiltin ∷ BuiltinT → Ident
identOfBuiltin = \case
  Tag → r "Tag"
  Bool → r "Bool"
  RowPlus → r "Row^"
  List → r "List"
  TypePlus → r "Type^"
  Eq → r "Eq"
  Refl → r "refl"
  RecordGet → r "record_get"
  RecordKeepFields → r "record_keep_fields"
  RecordDropFields → r "record_drop_fields"
  ListLength → r "list_length"
  ListIndexL → r "list_indexl"
  Fix' → r "fix"
  If → r "if"
  IntGte0 → r "int_>=0"
  IntEq → r "int_=="
  TagEq → r "tag_=="
  W → r "W"
  Wrap → r "wrap"
  Unwrap → r "unwrap"
  Never → r "Never"
  Any' → r "Any"
  Num d → r $ numDesc True d
  Add d → r $ numDesc False d <> "_add"
  Mul d → r $ numDesc False d <> "_mul"
  IntNeg d → r $ numDesc False d <> "_neg"
 where
  numDesc upper desc =
    (if upper then "I" else "i")
      <> case desc of
        NumFin nonneg bits →
          case bits of
            Bits8 → "8"
            Bits16 → "16"
            Bits32 → "32"
            Bits64 → "64"
            <> (if nonneg then "+" else mempty)
        NumInf → "nt"
  -- \| regular
  r x = x `Ident` False

pattern Op2 ∷ BuiltinT → Term → Term → TermF Term
pattern Op2 f a b = Term (Term (Builtin f) `App` a) `App` b

newtype Lambda a = Lambda {unLambda ∷ a}
  deriving (Show, Eq, Lift)

-- Vector + Lift
newtype Vector' a = Vector' (Vector a)
  deriving (Show, Eq, Ord, Eq1, Ord1, Functor, Foldable, Traversable, Semigroup)

instance IsList (Vector' a) where
  type Item (Vector' a) = a
  fromList = Vector' . fromList
  toList (Vector' v) = toList v

-- Need Lift a constraint for liftTyped [a]
instance (Lift a) ⇒ Lift (Vector' a) where
  liftTyped ∷ ∀ (m ∷ Type → Type). (TH.Quote m) ⇒ Vector' a → TH.Code m (Vector' a)
  liftTyped (Vector' v) =
    [||Vector' (fromList $$(liftTyped (toList v)))||]

data BlockF f
  = BlockLet !Quant !(Maybe Ident) !(Maybe f) !f !(Lambda f)
  | BlockRewrite !f !f
  deriving (Show, Eq, Lift)

data FieldsK a b = FRecord !a | FRow !b
  deriving (Show, Eq, Lift)

data RefineK a -- TODO: Permit Maybe Ident?
  = RefinePre !a !a
  | RefinePreTy !Ident !a !(Lambda a)
  | RefinePost !a !a
  | RefinePostTy !a !Ident !(Lambda a)
  deriving (Show, Eq, Lift)

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

data TermF a
  = -- Term-level
    NumLit !Integer
  | TagLit !Ident
  | BoolLit !Bool
  | ListLit !(Vector' a)
  | FieldsLit !(FieldsK () ()) !(Vector' (a, a))
  | BuiltinsVar
  | Builtin !BuiltinT
  | Lam !Quant !(Maybe Ident) !(Lambda a)
  | App !a !a
  | Var !Int
  | Sorry -- TODO: Pretty sure it should be destoyed in favour of application-scope existentials.
  | RefineGet !Int !(Int, Maybe Ident)
  | -- Erased
    Block !(BlockF a)
  | AppErased !a !a -- TODO: Maybe
  | Refine !(RefineK a)
  | Import !(Maybe Int {- resolved -}) !ByteString -- Erased from the perspective of `normalize`, kept by `compile`
  | -- Type-level
    Pi !Quant !(Maybe Ident) !a !(Lambda a)
  | Concat !a !(FieldsK a (Lambda a)) -- TODO: Demote Concat to builtin?
  | ExVar !(Int, Int)
  | UniVar !(Int, Int) !a
  deriving
    ( -- | ErasedAnn !Ident !Bool {\- postfix? -\} !a !(Lambda a) -- ^ Prefix erased overlay @|k : A| B
      Show
    , Eq
    , Lift
    )

newtype Term = Term {unTerm ∷ TermF Term}
  deriving (Show, Eq, Lift)

typOf ∷ Term → Term
typOf = Term . App (Term $ Builtin TypePlus)

rowOf ∷ Term → Term
rowOf u = Term $ App (Term $ Builtin RowPlus) u

recordGet ∷ Term → Term → Term
recordGet tag record = Term $ Term (Term (Builtin RecordGet) `App` tag) `App` record

typ ∷ Term
typ = typOf $ Term $ NumLit 0

eqOf ∷ Term → Term → Term
eqOf a b = Term $ Term (Term (Builtin Eq) `App` a) `App` b

maxOf ∷ Term → Term → Term
maxOf a b = Term (App (Term (App (Term (App (Term (Builtin If)) (Term (App (Term (Builtin IntGte0)) (Term (App (Term (App (Term (Builtin (Add NumInf))) (Term (App (Term (App (Term (Builtin (Mul NumInf))) (Term (NumLit (-1))))) b)))) a)))))) a)) b)

-- parsing

newtype IsErased = IsErased Bool
data ParserContext = ParserContext {pcErased ∷ !IsErased, pcBinds ∷ !(Vector (Quant, Maybe Ident))}
type Parser' = Parser ParserContext Pos

space ∷ Parser' ()
space =
  skipMany
    $ skipSatisfyAscii (\x → x == ' ' || x == '\n')
    <|> ($(string "//") *> skipMany (satisfyAscii (/= '\n')))

token ∷ Parser' a → Parser' a
token x = space *> x <* space

digit ∷ Parser' Integer
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

number ∷ Parser' Integer
number = token do
  sign ← optional $ $(char '-')
  val ← foldl' (\acc x → acc * 10 + x) 0 <$> some digit
  pure $ if isJust sign then (-val) else val

-- TODO: block words from ident' as well?.. probably not.
-- TODO: Convert blocklists to functions
identSym ∷ Parser' ()
identSym = skipSatisfy \x → x `notElem` (" \\/\n(){}[].:|" ∷ Vector Char)

-- Returns the identifier and whether it's an operator
-- Expect the ident to start RIGHT NOW.
identRightNow ∷ Parser' (Maybe Ident)
identRightNow = do
  rawResult ← byteStringOf (skipSome identSym)
  let (result, isOp) = case BS.uncons rawResult of
        Just ('_', rest)
          | Just (rest', '_') ← BS.unsnoc rest → (rest', True)
        _ → (rawResult, False)
  guard $ not $ BS.null result
  guard $ not $ "@" `BS.isPrefixOf` result
  -- TODO: Doesn't start with a number?
  guard $ result `notElem` (["Fun", "=", "in", "->", "unpack", "fadeno", "rewrite", "true", "false"] ∷ [ByteString])
  pure if result == "_" then Nothing else Just (Ident result isOp)

ident ∷ Parser' (Maybe Ident)
ident = token identRightNow

-- infxr ∷ Parser' a → Parser' (a → a → a) → Parser' a
-- infxr a oper = do
--   a' ← a
--   ( do
--       oper' ← oper
--       oper' a' <$> infxr a oper
--     )
--     <|> pure a'

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

-- -- Syntax is *a little* ambigious. I'm very sorry.

-- Standalone '='
parseEq ∷ Parser' Quant
parseEq = token $ notFollowedBy (q <* $(char '=')) identSym
 where
  q = ($(char '@') $> QEra) <|> pure QNorm

findVar ∷ ByteString → Parser' (Maybe (Int, Quant, Bool))
findVar name = do
  vars ← pcBinds <$> ask
  case findIndexR
    ( \(_, x) → case x of
        Just (Ident eName _) → eName == name
        _ → False
    )
    vars of
    Just ind →
      let (q, Ident _ eOp) = fmap (fromMaybe (error "impossible")) $ fromMaybe (error "impossible") $ vars !? ind
       in pure $ Just (length vars - ind - 1, q, eOp)
    Nothing → pure Nothing

localPathSym ∷ Parser' ()
localPathSym = skipSatisfyAscii \x → x `elem` ("abcdefghijklmnopqrstuvwxyz/" ∷ Vector Char)

-- Standalone `.` can be a variable introduced by the compiler.
dotvar ∷ Ident
dotvar = Ident "." False

-- 7
parsePrim ∷ Parser' Term
parsePrim = token do
  prim ←
    (Term . NumLit <$> number)
      <|> ( $(char '.')
              *> ( ($(char '/') *> (Term . Import Nothing <$> byteStringOf (skipSome localPathSym)))
                    <|> (Term . TagLit <$> (maybe failed pure =<< identRightNow))
                 )
          )
      <|> (Term . BoolLit <$> notFollowedBy ((True <$ $(string "true")) <|> (False <$ $(string "false"))) identSym)
      <|> ( do
              -- Record parsing
              isRow ← token ($(char '{') *> (isJust <$> optional $(char '(')))
              let parseField = do
                    n ← parsePrim
                    _todo ← parseEq
                    v ← parseTop
                    pure (n, v)
              knownFields ← fromList <$> sepBy (token $(char '|')) parseField
              token $ when isRow $(char ')') *> $(char '}')
              pure $ Term $ FieldsLit (if isRow then FRow () else FRecord ()) knownFields
          )
      <|> ( do
              token $(char '[')
              elems ← fromList <$> sepBy (token $(char '|')) (try parseTop)
              token $(char ']')
              pure $ Term $ ListLit elems
          )
      <|> (Term BuiltinsVar <$ notFollowedBy $(string "fadeno") identSym)
      <|> (Term Sorry <$ notFollowedBy ($(string "SORRY") <* many ($(char '!') <|> $(char '1'))) identSym)
      <|> ( Term <$> do
              -- Variable <|> RefineGet
              -- TODO: { x = 4 }
              let asDotvar = dotvar <$ notFollowedBy $(char '.') identSym
              Ident iName iOp ← asDotvar <|> (maybe failed pure =<< notFollowedBy identRightNow parseEq)
              IsErased isEra ← pcErased <$> ask
              i ←
                findVar iName >>= \case
                  Just (_, QEra, _) | not isEra → empty -- TODO: Still a crutch.
                  Just (n, _, eOp) → case (eOp, iOp) of
                    (True, False) → empty -- TODO: this is a crutch to stop user-defined operators from crashing the parser.
                    (False, True) → err =<< getPos
                    _ → pure n
                  Nothing → err =<< getPos -- TODO: better errors, overall
              let
                refineGets = do
                  skips ← many $ $(string ".@_")
                  final ← optional $ $(string ".@") *> (maybe failed pure =<< identRightNow)
                  when (isJust final && not isEra) failed -- TODO: Better error
                  when (null skips && isNothing final) failed
                  pure (length skips, final)
              (RefineGet i <$> refineGets) <|> pure (Var i)
          )
      <|> ( $(char '(') -- Parentheses parsing
              *> parseTop
              <* $(char ')')
          )
  -- any number of accesses after the prim
  accesses ← many $ $(char '.') *> (Term . TagLit <$> (maybe failed pure =<< identRightNow))
  pure
    $ foldl'
      (flip recordGet)
      prim
      accesses

insideEra ∷ ParserContext → ParserContext
insideEra x = x{pcErased = IsErased True}

withBind ∷ (Quant, Maybe Ident) → ParserContext → ParserContext
withBind b x = x{pcBinds = pcBinds x |> b}

-- 6
parseApp ∷ Parser' Term
parseApp = parsePrim >>= infxl'
 where
  infxl' prev =
    ( do
        space *> $(char '@')
        -- p ← ($(char '_') $> Nothing) <|> (Just <$> local insideEra parsePrim)
        p ← local insideEra parsePrim
        infxl' $ Term $ prev `AppErased` p
    )
      <|> ( do
              p ← parsePrim
              infxl' $ Term $ prev `App` p
          )
      <|> pure prev

-- 5
parseTy ∷ Parser' Term
parseTy =
  let
    parseAnn onTy onTerm = do
      token $(string "@|")
      let
        asTy = do
          etag ← maybe failed pure =<< ident
          token $(char ':')
          onTy etag
      res ← asTy <|> local insideEra onTerm
      token $(char '|')
      pure res
   in
    ( do
        token $(string "Fun")
        let
          getArg = do
            q ← token $ ($(char '(') $> QNorm) <|> ($(char '{') $> QEra)
            (n, t) ←
              ((,) <$> (ident <* token $(char ':')) <*> parseTop)
                <|> case q of
                  QNorm → (Nothing,) <$> parseTop
                  QEra → (,Term $ Builtin Any') . Just <$> (maybe failed pure =<< ident)
            token $ case q of
              QNorm → $(char ')')
              QEra → $(char '}')
            pure (q, n, t)
          getArgs1 = do
            (q, n, t) ← getArg
            Term . Pi q n t . Lambda <$> local (withBind (QNorm, n)) getArgs
          getArgs =
            ($(string "->") *> parseApp)
              <|> getArgs1
        getArgs1
    )
      <|> Term
      . Refine
      <$> do
        act ←
          parseAnn
            ( \etag → do
                annTy ← parseTop
                pure do
                  base ← Lambda <$> local (withBind (QNorm, Just etag)) parseTy
                  pure $ RefinePreTy etag annTy base
            )
            ( do
                ann ← parseTop
                pure $ RefinePre ann <$> parseTy
            )
        act
      <|> ( do
              -- Fused: parseApp <|> (\/) <|> (\./) <|> `parseApp @|...|`
              left ← parseApp
              space
              let
                asConcat = do
                  $(char '\\')
                  Term
                    . Concat left
                    <$> ( $(char '/')
                            *> (FRecord <$> parseTy)
                            <|> $(string "./")
                            *> (FRow . Lambda <$> local (withBind (QNorm, Just dotvar)) parseTy)
                        )
                asPostAnn =
                  Term
                    . Refine
                    <$> parseAnn
                      ( \etag → do
                          annTy ← Lambda <$> local (withBind (QNorm, Just dotvar)) parseTop
                          pure $ RefinePostTy left etag annTy
                      )
                      (RefinePost left <$> parseTop)
              asConcat <|> asPostAnn <|> pure left
          )

-- -- 4
parseInfixOps ∷ Parser' Term
parseInfixOps = infxl parseTy parseOperator'
 where
  parseOperator' ∷ Parser' (Term → Term → Term)
  parseOperator' = do
    i ← ident
    case i of
      Just (Ident opName False) →
        findVar opName >>= \case
          Just (idx, QNorm, True) → pure \a b → Term $ Term (Term (Var idx) `App` a) `App` b
          _ → empty -- Not a known operator in this scope
      _ → empty

insideQuant ∷ Quant → ParserContext → ParserContext
insideQuant = \case
  QEra → insideEra
  QNorm → id

-- -- 1
parseBlock ∷ Parser' Term
parseBlock = do
  let
    binding = do
      ty ← optional do
        token $(string "/:")
        local insideEra parseInfixOps
      name ← ident
      q ← parseEq
      IsErased isEra ← pcErased <$> ask
      when (isEra && q == QEra) failed -- TODO: Better error
      expr ← local (insideQuant q) parseTop
      pure (q, name, ty, expr)
    someEntries =
      ( do
          (q, name, ty, expr) ← binding
          rest ← Lambda <$> local (withBind (q, name)) manyEntries
          pure $ Term $ Block $ BlockLet q name ty expr rest
      )
        <|> ( do
                -- TODO: prettyprinting
                token $ $(string "unpack")
                record ← parsePrim
                token $ $(char '.')
                fieldNames ← some $ notFollowedBy (maybe failed pure =<< ident) parseEq
                foldr
                  (\name cont → Term . Block . BlockLet QNorm (Just name) Nothing (recordGet (Term $ TagLit name) record) . Lambda <$> local (withBind (QNorm, Just name)) cont)
                  manyEntries
                  fieldNames
            )
        <|> ( do
                token $ $(string "rewrite")
                rewrite ← local insideEra parseTop
                Term . Block . BlockRewrite rewrite <$> manyEntries
            )
    manyEntries =
      someEntries
        <|> ( do
                token $ $(string "in")
                parseTop
            )
  someEntries

-- 0
parseLam ∷ Parser' Term
parseLam = token do
  $(char '\\')
  idents ← some (token $ (,) <$> (($(char '@') $> QEra) <|> pure QNorm) <*> identRightNow)
  $(char '.')
  let
    parseBod = \case
      [] → parseTop
      (x : xs) → local (withBind x) $ parseBod xs
  bod ← parseBod idents
  pure $ foldr (\(q, n) → Term . Lam q n . Lambda) bod idents

-- 0
parseTop ∷ Parser' Term
parseTop =
  token
    $ parseBlock
    <|> parseLam
    <|> parseInfixOps
    <|> (err =<< getPos)

-- traversing

traverseTermF ∷ (Applicative m) ⇒ (a → m b) → (Lambda a → m (Lambda b)) → TermF a → m (TermF b)
traverseTermF c cNest = \case
  NumLit x → pure $ NumLit x
  TagLit x → pure $ TagLit x
  BoolLit x → pure $ BoolLit x
  ListLit (Vector' vec) → ListLit . Vector' <$> traverse c vec
  FieldsLit fi (Vector' vec) → FieldsLit fi . Vector' <$> traverse (bitraverse c c) vec
  Builtin x → pure $ Builtin x
  BuiltinsVar → pure BuiltinsVar
  Lam q arg bod → Lam q arg <$> cNest bod
  App f a → App <$> c f <*> c a
  Var i → pure $ Var i
  Sorry → pure Sorry
  Block (BlockLet q name ty val into) → Block <$> (BlockLet q name <$> traverse c ty <*> c val <*> cNest into)
  AppErased f a → AppErased <$> c f <*> c a
  Refine r →
    Refine <$> case r of
      RefinePre a b → RefinePre <$> c a <*> c b
      RefinePreTy n a b → RefinePreTy n <$> c a <*> cNest b
      RefinePost a b → RefinePost <$> c a <*> c b
      RefinePostTy a n b → RefinePostTy <$> c a <*> pure n <*> cNest b
  RefineGet b a → pure $ RefineGet b a
  Block (BlockRewrite prf into) → Block <$> (BlockRewrite <$> c prf <*> c into)
  Import resI x → pure $ Import resI x
  Pi q n inT outT → Pi q n <$> c inT <*> cNest outT
  Concat a b →
    Concat <$> c a <*> case b of
      FRecord b' → FRecord <$> c b'
      FRow b' → FRow <$> cNest b'
  ExVar i → pure $ ExVar i
  UniVar i t → UniVar i <$> c t

nestedBy' ∷ Int → Term → Int → Maybe Term
nestedBy' _ t00 0 = Just t00 -- optimization
nestedBy' locs0 t00 by =
  runIdentity
    $ runReader @Int locs0
    $ runEmpty (pure Nothing) (pure . Just)
    $ fix
      ( \rec t0 →
          let
            upd n = do
              locs ← R.ask
              if n >= locs
                then
                  if n + by >= 0
                    then pure $ n + by
                    else E.empty
                else pure n
           in
            Term <$> case unTerm t0 of
              Var n → Var <$> upd n
              RefineGet i s → (`RefineGet` s) <$> upd i
              t → traverseTermF rec (\t1 → Lambda <$> R.local @Int (+ 1) (rec $ unLambda t1)) t
      )
      t00

nestedByP' ∷ Int → Term → Int → Term
nestedByP' locs t by = fromMaybe (error "Expected positive nesting") $ nestedBy' locs t by

nestedByP ∷ Term → Int → Term
nestedByP = nestedByP' 0

nested ∷ Term → Term
nested = (`nestedByP` 1)

-- printing

pBS ∷ ByteString → Doc AnsiStyle
pBS = pretty . decodeUtf8Lenient

pIdent ∷ Ident → Doc AnsiStyle
pIdent (Ident x isOp) =
  let res = pBS x
   in if isOp then "_" <> res <> "_" else res

-- Left/right?
withPrec ∷ Int → (Int, Doc ann) → Doc ann
withPrec oldPrec (newPrec, bod) =
  if oldPrec > newPrec
    then "(" <> bod <> ")"
    else bod

complexThreshold ∷ Int → Bool
complexThreshold = (>= 5)

-- TODO: Stop it. Just count real symbols.
isSimple ∷ Term → Bool
isSimple =
  let ping = do
        modify @Int (+ 1)
        curr ← get
        when (complexThreshold curr) E.empty
      tlComplexity =
        complexity . \case
          FRecord b' → b'
          FRow b' → unLambda b'
      complexity =
        unTerm >>> \case
          Lam _ _ (Lambda x) → ping *> complexity x
          Block defs →
            ping
              *> ( case defs of
                    BlockLet _ _ b c x → for_ b complexity *> complexity c *> complexity (unLambda x)
                    BlockRewrite r x → ping *> complexity r *> complexity x
                 )
          App f a → complexity f *> complexity a
          AppErased f a → complexity f *> complexity a
          Refine r → case r of
            RefinePre a b → complexity a *> complexity b
            RefinePreTy _ a b → ping *> complexity a *> complexity (unLambda b)
            RefinePost a b → complexity a *> complexity b
            RefinePostTy a _ b → ping *> complexity a *> complexity (unLambda b)
          RefineGet _ _ → ping
          Import _ _ → ping
          NumLit _ → ping
          TagLit _ → ping
          BoolLit _ → ping
          Sorry → ping
          Var _ → ping
          ListLit vs → ping *> traverse_ complexity vs
          FieldsLit _ fields → ping *> traverse_ (\(k, v) → complexity k *> complexity v) fields
          Pi _ _ b c → ping *> complexity b *> complexity (unLambda c)
          Concat a b → complexity a *> tlComplexity b
          Builtin _ → ping
          BuiltinsVar → ping
          ExVar _ → ping
          UniVar _ t → ping *> complexity t
   in runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

pQuant ∷ Quant → Doc AnsiStyle
pQuant = \case
  QEra → "@"
  QNorm → mempty

data Fuse = FNo | FLam | FPi | FBlock !(Maybe Term) deriving (Eq)

-- TODO: Refactor isSimple, it's frankly stupid.
-- Refactor the whole system, it's all stupid.
pTerm' ∷ (Fuse, Int, Vector (Maybe Ident)) → Term → Doc AnsiStyle
pTerm' (fuse, oldPrec, vars) t0 =
  let
    pvar x = maybe ("#" <> pretty x) (maybe "_" pIdent) (vars !? (length vars - x - 1))
    prefixf = case (fuse, unTerm t0) of
      (FNo, _) → id
      (FLam, Lam{}) → id
      (FLam, _) → (<>) $ annotate (color Cyan) "." <> if isSimple t0 then " " else line
      (FPi, Pi{}) → id
      (FPi, _) → (<>) $ annotate (color Cyan) "->" <> " "
      (FBlock _, Block{}) → id
      (FBlock _, _) → \x → line <> annotate (color Cyan) "in" <+> nest 2 x
   in
    prefixf $ withPrec oldPrec case unTerm t0 of
      Lam q arg x →
        ( 0
        , (if fuse == FLam then " " else annotate (color Cyan) "\\")
            <> pQuant q
            <> maybe "_" pIdent arg
            <> pTerm' (FLam, 0, vars |> arg) (unLambda x)
        )
      Block block → (1,) $ case block of
        BlockLet q nameM tyM val in_ →
          case (tyM, nameM, val) of
            (Nothing, Just name1, unTerm → (unTerm → (unTerm → Builtin RecordGet) `App` (unTerm → TagLit name2)) `App` record)
              | name1 == name2 →
                  (if fuse == FBlock (Just record) then mempty else annotate (color Yellow) "unpack" <+> pTerm' (FNo, 5, vars) record <> annotate (color Cyan) ".")
                    <+> pIdent name1
                      <> pTerm' (FBlock $ Just record, 0, vars |> Just name1) (unLambda in_)
            _ →
              ( case fuse of
                  FBlock{} → line
                  _ → mempty
              )
                <> maybe
                  mempty
                  ( \ty →
                      ( case fuse of
                          FBlock{} → line
                          _ → mempty
                      )
                        <> "/:"
                        <+> nest 2 (pTerm' (FNo, 2, vars) ty) <> line
                  )
                  tyM -- TODO: split if complicated type
                <> maybe "_" pIdent nameM
                <+> annotate (color Yellow) (pQuant q <> "=")
                  <> softline
                  <> nest 2 (pTerm' (FNo, 0, vars) val)
                  <> pTerm' (FBlock Nothing, 0, vars |> nameM) (unLambda in_)
        BlockRewrite x in_ → line <> "rewrite" <+> pTerm' (FNo, 0, vars) x <> line <> pTerm' (FBlock Nothing, 0, vars) in_
      Pi q name inTy outTy →
        ( 3
        , let (bL, bR) = case q of
                QNorm → ("(", ")")
                QEra → ("{", "}")
           in (if fuse == FPi then mempty else annotate (color Cyan) "Fun" <> " ")
                <> bL
                <> maybe mempty (\i → pIdent i <+> ": ") name
                <> pTerm' (FNo, 0, vars) inTy
                <> bR
                <+> pTerm' (FPi, 3, vars |> name) (unLambda outTy)
        )
      Concat a b →
        ( 3
        , pTerm' (FNo, 4, vars) a
            <+> annotate (color Cyan) "\\" <> case b of
              FRecord b' → annotate (color Cyan) "/" <+> pTerm' (FNo, 3, vars) b'
              FRow b' → "." <> annotate (color Cyan) "/" <+> pTerm' (FNo, 3, vars |> Just dotvar) (unLambda b')
        )
      Refine r →
        let
          pBase fvars = pTerm' (FNo, 3, fvars vars)
          pATy n fvars t = pIdent n <+> annotate (color Cyan) ":" <+> pTerm' (FNo, 0, fvars vars) t
          pATerm fvars = pTerm' (FNo, 0, fvars vars)
          pAnn x = annotate (color Cyan) "@|" <> x <> annotate (color Cyan) "|"
         in
          ( 3
          , case r of
              RefinePre ann base → pAnn (pATerm id ann) <+> pBase id base
              RefinePreTy n annTy base → pAnn (pATy n id annTy) <+> pBase (|> Just n) (unLambda base)
              RefinePost base ann → pBase id base <+> pAnn (pATerm id ann)
              RefinePostTy base n annTy → pBase id base <+> pAnn (pATy n (|> Just dotvar) $ unLambda annTy)
          )
      Sorry → (5, "SORRY!")
      RefineGet x (skips, final) →
        let skips' = hcat $ replicate skips ".@_"
         in (5, pvar x <> annotate (color Blue) (skips' <> maybe mempty (\final' → ".@" <> pIdent final') final))
      App (unTerm → App (unTerm → Builtin RecordGet) (unTerm → TagLit tag)) rec →
        (5, pTerm' (FNo, 5, vars) rec <> annotate (color Blue) ("." <> pIdent tag))
      App lam arg2 → case lam of
        (unTerm → App (unTerm → Var opIdx) arg1)
          | Just (Just (Ident opName True)) ← vars !? (length vars - opIdx - 1) →
              (2, pTerm' (FNo, 3, vars) arg1 <+> pBS opName <+> pTerm' (FNo, 2, vars) arg2)
        _ →
          (4, pTerm' (FNo, 4, vars) lam <+> pTerm' (FNo, 5, vars) arg2)
      AppErased lam arg → (4, pTerm' (FNo, 4, vars) lam <+> "@" <> pTerm' (FNo, 5, vars) arg)
      Builtin x → (5, "fadeno." <> annotate (color Green) (pIdent (identOfBuiltin x)))
      BuiltinsVar → (5, "fadeno")
      NumLit x → (5, pretty x)
      BoolLit x → (5, annotate (color Green) if x then "true" else "false")
      TagLit x → (5, annotate (color Blue) $ "." <> pIdent x)
      FieldsLit fi fields →
        let (brL, brR) = case fi of
              FRecord () → ("{", "}")
              FRow () → ("{(", ")}")
         in ( 5
            , encloseSep
                (annotate (color White) brL)
                (annotate (color White) brR)
                (annotate (color White) " | ")
                (fmap (\(n, v) → pTerm' (FNo, 5, vars) n <+> annotate (color Cyan) "=" <+> pTerm' (FNo, 0, vars) v) (toList fields))
            )
      ListLit vec → (5, encloseSep "[" "]" " | " $ pTerm' (FNo, 0, vars) <$> toList vec)
      Var x → (5, pvar x)
      Import _ x → (5, "./" <> pBS x)
      ExVar (s, i) → (5, "(exi#" <> pretty s <> "/" <> pretty i <> ")")
      UniVar (s, i) t → (5, "(uni#" <> pretty s <> "/" <> pretty i <+> ":" <+> pTerm' (FNo, 0, vars) t <> ")")

pTerm ∷ Vector (Maybe Ident) → Term → Doc AnsiStyle
pTerm = pTerm' . (FNo,0,)

parse ∷ ParserContext → ByteString → Either Text Term
parse vars inp = case runParser (parseTop <* eof) vars 0 inp of
  OK x _ "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error: parser failure"

parseSource ∷ ByteString → IO Term
parseSource x = pure $ either (error . show) id $ parse (ParserContext (IsErased False) []) x

parseFile ∷ OsPath → IO Term
parseFile = parseSource <=< readFile'

render ∷ Doc AnsiStyle → IO ()
render x = renderIO stdout $ layoutSmart defaultLayoutOptions $ x <> line

formatSource ∷ ByteString → IO ()
formatSource = render . pTerm [] <=< parseSource

formatFile ∷ OsPath → IO ()
formatFile = formatSource <=< readFile'

type LoaderC = StateC (HashMap OsPath Int) (StateC N.UsedNames (StateC (Vector Term) IO))
newtype Module = Module (Vector Term) -- non-empty

-- TODO: disallow trailing `/` in Import syntax!
loadModule' ∷ OsPath → IO (N.UsedNames, Module)
loadModule' = runState (\t u → pure (u, Module t)) [] . execState N.emptyUsedNames . evalState mempty . new
 where
  new ∷ OsPath → LoaderC ()
  new path = do
    t0 ← sendIO $ parseFile $ path <> unsafeEncodeUtf ".fad"
    t ← runReader path $ subload t0
    modify (|> t)
    get @(Vector Term) >>= \ms → modify @(HashMap OsPath Int) $ HM.insert path $ length ms - 1
  subload ∷ Term → ReaderC OsPath LoaderC Term
  subload =
    unTerm >>> \case
      Import Nothing subpath → do
        dir ← R.ask
        subpath' ← sendIO $ encodeUtf (BS.unpack subpath)
        let path = takeDirectory dir </> subpath'
        loaded ← get
        i ← case HM.lookup path loaded of
          Just i → pure i
          Nothing → do
            RIO.lift $ new path
            (\x → length x - 1) <$> get @(Vector Term)
        pure $ Term $ Import (Just i) subpath
      t → do
        let
          label = case t of
            Block (BlockLet _ (Just (Ident n False)) _ _ _) → Just n
            Lam _ (Just (Ident n False)) _ → Just n
            Pi _ (Just (Ident n False)) _ _ → Just n
            _ → Nothing
        for_ label $ modify . N.use
        Term <$> traverseTermF subload (fmap Lambda . subload . unLambda) t

loadModule ∷ FilePath → IO (N.UsedNames, Module)
loadModule = encodeUtf >=> loadModule'

formatModule ∷ Module → IO ()
formatModule (Module m) =
  render
    $ vsep
    $ fmap
      (\(i, t) → "/" <> pretty i <> nest 1 (line <> pTerm [] t))
      (toList $ zip [0 .. length m - 1] m)

parseQQ ∷ QuasiQuoter
parseQQ =
  QuasiQuoter
    { quoteExp = \s → do
        term ← case parse (ParserContext (IsErased False) []) (BS.pack s) of
          Left e → fail $ "parseQQ: Parse error: " ++ show e
          Right t → pure t
        ⟦term⟧
    , quotePat = error "parseQQ: No pattern support"
    , quoteType = error "parseQQ: No type support"
    , quoteDec = error "parseQQ: No declaration support"
    }

freshIdent ∷ (Has (State N.UsedNames) sig m) ⇒ m Ident
freshIdent = (`Ident` False) <$> N.genM
