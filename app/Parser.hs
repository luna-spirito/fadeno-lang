module Parser (
  Binding,
  Bits (..),
  BlockF (..),
  BuiltinT (..),
  ContextEntry (..),
  Fields (..),
  Ident (..),
  Lambda (..),
  N (..),
  NumDesc (..),
  Quant (..),
  Term (..),
  TermF (..),
  Vector' (..),
  builtinsList,
  ctxFindBinding,
  ctxFindEx,
  eqOf,
  formatFile,
  identOfBuiltin,
  intercept,
  nestedBy',
  nestedByP,
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
  unwrap,
) where

import Control.Algebra
import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.Reader (runReader)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Carrier.Writer.Church (Writer, censor, listen)
import Control.Effect.Empty qualified as E
import Control.Effect.Reader qualified as R
import Data.ByteString.Char8 qualified as BS
import Data.Kind (Type)
import Data.RRBVector (Vector, findIndexR, ifoldl', viewl, (!?), (|>))
import FlatParse.Stateful (Parser, Pos, Result (..), anyAsciiChar, ask, byteStringOf, char, empty, eof, err, failed, getPos, local, notFollowedBy, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSatisfyAscii, skipSome, string, try)
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Syntax (Lift (..))
import Language.Haskell.TH.Syntax qualified as TH
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, encloseSep, layoutSmart, line, nest, softline, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, Vector, ask, local, runReader, toList, try)

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
  deriving (Show, Eq, Lift)

data Bits = Bits8 | Bits16 | Bits32 | Bits64 | BitsInf
  deriving (Show, Eq, Ord, Lift)
data NumDesc = NumDesc !Bool {- ≥ 0 -} !Bits
  deriving (Show, Eq, Lift)

data BuiltinT
  = Tag
  | Row
  | List
  | Bool
  | TypePlus -- Type+ 0, Type+ 1, ..., Type+ Aleph
  | Eq
  | Refl
  | RecordGet -- Second-class!
  | RecordKeepFields
  | RecordDropFields
  | ListLength
  | ListIndexL
  | NatFold
  | If -- TODO: Make Choice counterpart for Record
  | IntGte0
  | IntEq
  | IntNeq
  | TagEq
  | W
  | Wrap
  | Unwrap
  | Never
  | Any'
  | Add !NumDesc
  | Num !NumDesc
  | IntNeg !NumDesc
  deriving (Show, Eq, Lift)

builtinsList ∷ Vector BuiltinT
builtinsList =
  [Tag, Row, List, Bool, TypePlus, Eq, Refl, RecordGet, RecordKeepFields, RecordDropFields, ListLength, ListIndexL, NatFold, If, IntGte0, IntEq, TagEq, W, Wrap, Unwrap, Never, Any']
    <> (Num <$> nd)
    <> (Add <$> ndSansIntP)
    <> (IntNeg <$> ndSansIntP)
 where
  ndFins = (NumDesc <$> [False, True] <*> [Bits8, Bits16, Bits32, Bits64])
  ndSansIntP = ndFins <> [NumDesc False BitsInf]
  nd = ndSansIntP <> [NumDesc True BitsInf]

identOfBuiltin ∷ BuiltinT → Ident
identOfBuiltin = \case
  Add d → r $ numDesc False d <> "_add"
  IntNeg d → r $ numDesc False d <> "_neg"
  Num d → r $ numDesc True d
  Tag → r "Tag"
  Bool → r "Bool"
  Row → r "Row"
  List → r "List"
  TypePlus → r "Type+"
  Eq → r "Eq"
  Refl → r "refl"
  RecordGet → r "record_get"
  RecordKeepFields → r "record_keep_fields"
  RecordDropFields → r "record_drop_fields"
  ListLength → r "list_length"
  ListIndexL → r "list_indexl"
  NatFold → r "~int+_fold"
  If → r "if"
  IntGte0 → r "int_>=0"
  IntEq → r "int_/="
  IntNeq → r "int_=="
  TagEq → r "tag_=="
  W → r "W"
  Wrap → r "wrap"
  Unwrap → r "unwrap"
  Never → r "Never"
  Any' → r "Any"
 where
  numDesc upper (NumDesc nonneg bits) =
    (if upper then "I" else "i")
      <> ( case bits of
            Bits8 → "8"
            Bits16 → "16"
            Bits32 → "32"
            Bits64 → "64"
            BitsInf → "nt"
         )
      <> (if nonneg then "+" else mempty)
  -- \| regular
  r x = x `Ident` False

newtype Lambda a = Lambda {unLambda ∷ a}
  deriving (Show, Eq, Lift)

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

data BlockF f
  = BlockLet !Quant !(Maybe Ident) !(Maybe f) !Term !(Lambda f)
  | BlockRewrite !f !f
  deriving (Show, Eq, Lift)

data Fields a b = FRecord !a | FRow !b
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
  | FieldsLit !(Fields () ()) !(Vector' (a, a))
  | BuiltinsVar
  | Builtin !BuiltinT
  | Lam !Quant !(Maybe Ident) !(Lambda a)
  | App !a !a
  | Var !Int
  | Sorry
  | -- Erased
    AppErased !a !a -- TODO: Maybe
  | Block !(BlockF a)
  | -- Type-level
    Pi !Quant !(Maybe Ident) !a !(Lambda a) -- TODO: Demote Pi and Concat to builtins?
  | Concat !a !(Fields a (Maybe Ident, Lambda a))
  | ExVar !Int
  | UniVar !Int
  deriving (Show, Eq, Lift)

newtype Term = Term {unTerm ∷ TermF Term}
  deriving (Show, Eq, Lift)

typOf ∷ Term → Term
typOf = Term . App (Term $ Builtin TypePlus)

rowOf ∷ Term → Term
rowOf = Term . App (Term $ Builtin Row)

recordGet ∷ Term → Term → Term
recordGet tag record = Term $ (Term $ (Term $ Builtin RecordGet) `App` tag) `App` record

typ ∷ Term
typ = typOf $ Term $ NumLit 0

eqOf ∷ Term → Term → Term
eqOf a b = Term $ Term ((Term $ Builtin Eq) `App` a) `App` b

-- parsing

type ParserContext = Vector (Quant, Maybe Ident)
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
identSym ∷ Parser' Char
identSym = satisfy \x → not $ x `elem` (" \\/\n(){}[].:|" ∷ String)

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
  guard $ not $ result `elem` (["Fun", "=", "in", "->", "unpack", "fadeno", "rewrite", "true", "false"] ∷ [ByteString])
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
  vars ← ask
  case findIndexR
    ( \(_, x) → case x of
        Just (Ident eName _) → eName == name
        _ → False
    )
    vars of
    Just n →
      let (q, Ident _ eOp) = fmap (fromMaybe (error "impossible")) $ fromMaybe (error "impossible") $ vars !? n
       in pure $ Just (n, q, eOp)
    Nothing → pure Nothing

-- 7
parsePrim ∷ Parser' Term
parsePrim = token do
  prim ←
    (Term . NumLit <$> number)
      <|> (Term . TagLit <$> ($(char '.') *> (maybe failed pure =<< identRightNow)))
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
              token $ (when isRow $(char ')')) *> $(char '}')
              pure $ Term $ FieldsLit (if isRow then FRow () else FRecord ()) knownFields
          )
      <|> ( do
              token $(char '[')
              elems ← fromList <$> sepBy (token $(char '|')) (try parseTop)
              token $(char ']')
              pure $ Term $ ListLit elems
          )
      <|> (Term BuiltinsVar <$ (notFollowedBy $(string "fadeno") identSym))
      <|> (Term Sorry <$ notFollowedBy ($(string "SORRY") <* many ($(char '!') <|> $(char '1'))) identSym)
      <|> ( Term . Var <$> do
              -- Variable parsing
              -- TODO: { x = 4 }
              Ident iName iOp ← maybe failed pure =<< notFollowedBy ident parseEq
              findVar iName >>= \case
                Just (_, QEra, _) → empty -- TODO: Still a crutch.
                Just (n, QNorm, eOp) → case (eOp, iOp) of
                  (True, False) → empty -- TODO: this is a crutch to stop user-defined operators from crashing the parser.
                  (False, True) → err =<< getPos
                  _ → pure n
                Nothing → err =<< getPos -- TODO: better errors, overall
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
insideEra = fmap $ first \_ → QNorm

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
  ( do
      token $(string "Fun")
      let
        getArg = do
          q ← token $ ($(char '(') $> QNorm) <|> ($(char '{') $> QEra)
          (n, t) ←
            ((,) <$> (ident <* token $(char ':')) <*> parseTop)
              <|> case q of
                QNorm → ((Nothing,) <$> parseTop)
                QEra → ((,Term $ Builtin Any') . Just <$> (maybe failed pure =<< ident))
          token $ case q of
            QNorm → $(char ')')
            QEra → $(char '}')
          pure (q, n, t)
        getArgs1 = do
          (q, n, t) ← getArg
          Term . Pi q n t . Lambda <$> local (|> (QNorm, n)) getArgs
        getArgs =
          (($(string "->") *> parseApp))
            <|> getArgs1
      getArgs1
  )
    <|> ( do
            -- Fused: parseApp <|> (\/)
            left ← parseApp
            ( ( do
                  iM ← token do
                    $(char '\\')
                    optional identRightNow <* $(char '/')
                  Term . Concat left <$> case iM of
                    Nothing → FRecord <$> parseTy
                    Just i → FRow . (i,) . Lambda <$> local (|> (QNorm, i)) parseTy
              )
                <|> pure left
              )
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
          Just (idx, QNorm, True) → pure \a b → Term $ (Term $ (Term $ Var idx) `App` a) `App` b
          _ → empty -- Not a known operator in this scope
      _ → empty

insideLet ∷ Quant → ParserContext → ParserContext
insideLet = \case
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
      expr ← local (insideLet q) $ parseTop
      pure (q, name, ty, expr)
    someEntries =
      ( do
          (q, name, ty, expr) ← binding
          rest ← Lambda <$> (local (|> (q, name)) manyEntries)
          pure $ Term $ Block $ BlockLet q name ty expr rest
      )
        <|> ( do
                -- TODO: prettyprinting
                token $ $(string "unpack")
                record ← parsePrim
                token $ $(char '.')
                fieldNames ← some $ notFollowedBy (maybe failed pure =<< ident) parseEq
                foldr
                  (\name cont → Term . Block . BlockLet QNorm (Just name) Nothing (recordGet (Term $ TagLit name) record) . Lambda <$> local (|> (QNorm, Just name)) cont)
                  manyEntries
                  fieldNames
            )
        <|> ( do
                token $ $(string "rewrite")
                rewrite ← parseTop
                rest ← manyEntries
                pure $ Term $ Block (BlockRewrite rewrite rest)
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
      (x : xs) → local (|> x) $ parseBod xs
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

-- context

-- A value normalized IN THE CURRENT CONTEXT. Unsafe, obviously
newtype N a = N {unN ∷ a}

type Binding = (Quant, Maybe Ident, Maybe Term, Term)
data ContextEntry = ContextBinding !Binding | ContextMarker | ContextExVar !Int !(Either Term Term) -- (value/type)

traverseTermF ∷ (Applicative m) ⇒ (Term → m Term) → (Lambda Term → m (Lambda Term)) → TermF Term → m (TermF Term)
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
  AppErased f a → AppErased <$> c f <*> c a
  Block (BlockLet q name ty val into) → Block <$> (BlockLet q name <$> traverse c ty <*> c val <*> cNest into)
  Block (BlockRewrite prf into) → Block <$> (BlockRewrite <$> c prf <*> c into)
  Pi q n inT outT → Pi q n <$> c inT <*> cNest outT
  Concat a b →
    Concat <$> c a <*> case b of
      FRecord b' → FRecord <$> c b'
      FRow (i, b') → FRow . (i,) <$> cNest b'
  ExVar i → pure $ ExVar i
  UniVar i → pure $ UniVar i

nestedBy' ∷ Term → Int → Maybe Term
nestedBy' t00 0 = Just t00 -- optimization
nestedBy' t00 by =
  runIdentity
    $ runReader @Int 0
    $ runEmpty (pure Nothing) (pure . Just)
    $ fix
      ( \rec t0 →
          Term <$> case unTerm t0 of
            Var n → do
              locs ← R.ask
              if n >= locs
                then
                  if n + by >= 0
                    then pure $ Var $ n + by
                    else E.empty
                else pure $ Var n
            t → traverseTermF rec (\t1 → Lambda <$> R.local @Int (+ 1) (rec $ unLambda t1)) t
      )
      t00

nestedByP ∷ Term → Int → Term
nestedByP t by = fromMaybe (error "Expected positive nesting") $ nestedBy' t by

-- Side note: sounds like a good function to design effect system around?
ctxFindEx ∷ Int → Vector ContextEntry → (Term, Int)
ctxFindEx =
  flip
    $ foldl'
      ( \rec entry i → case entry of
          ContextBinding _ → fmap (+ 1) $ rec i
          ContextExVar i2 valty | i == i2 → case valty of
            Left (Term (ExVar j)) → rec j
            Left val → (val, 0)
            Right _ → (Term $ ExVar i, 0)
          _ → rec i
      )
      (\i → (Term $ ExVar i, 0))

ctxResolveEx ∷ Int → Vector ContextEntry → TermF Term
ctxResolveEx i0 ctx =
  let (resolved, depth) = ctxFindEx i0 ctx
   in unTerm $ resolved `nestedByP` depth

unwrap ∷ Vector ContextEntry → Term → TermF Term
unwrap ctx =
  unTerm >>> \case
    ExVar i → ctxResolveEx i ctx
    x → x

ctxFindBinding ∷ Int → Vector ContextEntry → Maybe Binding
ctxFindBinding i0 ctx0 =
  foldl'
    ( \rec entry i → case entry of
        ContextBinding b → if i == 0 then Just b else rec $ i - 1
        _ → rec i
    )
    (\_ → Nothing)
    ctx0
    i0

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

isSimple ∷ Vector ContextEntry → Term → Bool
isSimple ctx0 =
  let ping = do
        modify @Int (+ 1)
        curr ← get
        if complexThreshold curr
          then E.empty
          else pure ()
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
          NumLit _ → ping
          TagLit _ → ping
          BoolLit _ → ping
          Sorry → ping
          Var _ → ping
          ListLit vs → ping *> traverse_ complexity vs
          FieldsLit _ fields → ping *> traverse_ (\(k, v) → complexity k *> complexity v) fields
          Pi _ _ b c → ping *> complexity b *> complexity (unLambda c)
          Concat a b →
            complexity a *> complexity case b of
              FRecord b' → b'
              FRow (_, b') → unLambda b'
          Builtin _ → ping
          BuiltinsVar → ping
          ExVar i → case unTerm $ fst $ ctxFindEx i ctx0 of
            ExVar _ → ping
            x → complexity $ Term x
          UniVar _ → ping
   in runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

pQuant ∷ Quant → Doc AnsiStyle
pQuant = \case
  QEra → "@"
  QNorm → mempty

data Fuse = FNo | FLam | FPi | FBlock !(Maybe Term) deriving (Eq)

-- TODO: Refactor isSimple, it's frankly stupid.
-- Refactor the whole system, it's all stupid.
pTerm' ∷ (Fuse, Int, Vector ContextEntry) → Term → Doc AnsiStyle
pTerm' (fuse, oldPrec, vars) t0 =
  let
    newBind arg = ContextBinding (QNorm, arg, Nothing, Term $ Builtin Any') -- don't care about the specifics
    tf0 = unwrap vars t0
    prefixf = case (fuse, tf0) of
      (FNo, _) → id
      (FLam, Lam{}) → id
      (FLam, _) → (<>) $ annotate (color Cyan) "." <> if isSimple vars (Term tf0) then " " else line
      (FPi, Pi{}) → id
      (FPi, _) → (<>) $ annotate (color Cyan) "->" <> " "
      (FBlock _, Block{}) → id
      (FBlock _, _) → \x → line <> annotate (color Cyan) "in" <+> nest 2 x
   in
    prefixf $ withPrec oldPrec case tf0 of
      Lam q arg x →
        ( 0
        , (if fuse == FLam then " " else annotate (color Cyan) "\\")
            <> pQuant q
            <> maybe "_" pIdent arg
            <> pTerm' (FLam, 0, vars) (unLambda x)
        )
      Block block → (1,) $ case block of
        BlockLet q nameM tyM val in_ →
          case (tyM, nameM, val) of
            (Nothing, Just name1, unwrap vars → (unwrap vars → (unwrap vars → Builtin RecordGet) `App` (unwrap vars → TagLit name2)) `App` record)
              | name1 == name2 →
                  (if fuse == FBlock (Just record) then mempty else annotate (color Yellow) "unpack" <+> pTerm' (FNo, 5, vars) record <> annotate (color Cyan) ".")
                    <+> pIdent name1
                      <> pTerm' (FBlock $ Just record, 0, vars |> newBind (Just name1)) (unLambda in_)
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
                  <> pTerm' (FBlock Nothing, 0, vars |> newBind nameM) (unLambda in_)
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
                <+> pTerm' (FPi, 3, vars |> newBind name) (unLambda outTy)
        )
      Concat a b →
        ( 3
        , pTerm' (FNo, 4, vars) a
            <+> annotate (color Cyan) "\\" <> case b of
              FRecord b' → annotate (color Cyan) "/" <+> pTerm' (FNo, 3, vars) b'
              FRow (n, b') → maybe "_" pIdent n <> annotate (color Cyan) "/" <+> pTerm' (FNo, 3, vars |> newBind n) (unLambda b')
        )
      Sorry → (5, "SORRY!")
      App (unwrap vars → App (unwrap vars → Builtin RecordGet) (unwrap vars → TagLit tag)) rec →
        (5, pTerm' (FNo, 5, vars) rec <> annotate (color Blue) ("." <> pIdent tag))
      App lam arg2 → case lam of
        (unwrap vars → App (unwrap vars → Var opIdx) arg1)
          | Just (_, Just (Ident opName True), _, _) ← ctxFindBinding opIdx vars →
              (2, pTerm' (FNo, 3, vars) arg1 <+> pBS opName <+> pTerm' (FNo, 2, vars) arg2)
        _ →
          (4, pTerm' (FNo, 4, vars) lam <+> pTerm' (FNo, 5, vars) arg2)
      AppErased lam arg → (4, pTerm' (FNo, 4, vars) lam <+> "@" <> pTerm' (FNo, 5, vars) arg)
      Builtin x → (5, "fadeno." <> pIdent (identOfBuiltin x))
      BuiltinsVar → (5, "fadeno")
      NumLit x → (5, pretty x)
      BoolLit x → (5, if x then "true" else "false")
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
      ListLit vec → (5, encloseSep "[" "]" " | " $ fmap (\x → pTerm' (FNo, 0, vars) x) (toList vec))
      Var x → (5, maybe ("#" <> pretty x) (\(_, i, _, _) → maybe "_" pIdent i) $ ctxFindBinding x vars)
      ExVar (a, b) → (5, "(exi#" <> pretty a <> "/" <> pretty (toList b) <> ")")
      UniVar i → (5, "(uni#" <> pretty i <> ")")

pTerm ∷ Vector ContextEntry → Term → Doc AnsiStyle
pTerm = pTerm' . (FNo,0,)

parse ∷ ParserContext → ByteString → Either Text Term
parse vars inp = case runParser (parseTop <* eof) vars 0 inp of
  OK x _ "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error:  failure"

parseSource ∷ ByteString → IO Term
parseSource x = pure $ either (error . show) id $ parse [] x

parseFile ∷ FilePath → IO Term
parseFile = parseSource <=< readFileBinary

render ∷ Doc AnsiStyle → IO ()
render x = renderIO stdout $ layoutSmart defaultLayoutOptions $ x <> line

formatSource ∷ ByteString → IO ()
formatSource = render . pTerm [] <=< parseSource

formatFile ∷ FilePath → IO ()
formatFile = formatSource <=< readFileBinary
