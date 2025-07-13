module Parser (
  Bits (..),
  BlockT (..),
  BuiltinT (..),
  ExType (..),
  ExVarId (..),
  Ident (..),
  Lambda (..),
  Quant (..),
  NumDesc (..),
  TermT (..),
  Vector' (..),
  builtinsList,
  eqOf,
  formatFile,
  identOfBuiltin,
  pIdent,
  pQuant,
  pTerm',
  parse,
  parseFile,
  recordGet,
  recordOf,
  render,
  rowOf,
  typ,
  typOf,
) where

import Control.Carrier.Empty.Church (runEmpty)
import Control.Carrier.State.Church (evalState, get, modify)
import Control.Effect.Empty qualified as E
import Data.ByteString.Char8 qualified as BS
import Data.Hashable (Hashable (..))
import Data.Kind (Type)
import Data.RRBVector (Vector, findIndexL, (!?), (<|))
import FlatParse.Stateful (Parser, Pos, Result (..), anyAsciiChar, ask, byteStringOf, char, empty, eof, err, failed, getPos, local, notFollowedBy, posLineCols, runParser, satisfy, satisfyAscii, skipMany, skipSatisfyAscii, skipSome, string, try)
import GHC.Exts (IsList (..))
import Language.Haskell.TH.Syntax (Lift (..))
import Language.Haskell.TH.Syntax qualified as TH
import Prettyprinter (Doc, Pretty (..), annotate, defaultLayoutOptions, encloseSep, layoutSmart, line, nest, softline, vsep, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, renderIO)
import RIO hiding (Reader, Vector, ask, local, toList, try)

-- TODO ASAP: assocativity for operators. YeAh, TuRns oUT wE NeEd iT, wHo coUlD hAvE GuESseD?
-- (6 - 4 - 2 ≠ 6 - (4 - 2))

data Ident = Ident !ByteString !Bool -- raw name, is operator
  deriving (Show, Eq, Ord, Generic, Lift)

data Quant = QEra | QNorm
  deriving (Show, Eq, Lift)

instance Hashable Ident

type ParserContext = Vector (Quant, Ident)
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
identSym = satisfy \x → not $ x `elem` ("\\ \n(){}[].:|" ∷ String)

-- Returns the identifier and whether it's an operator
-- Expect the ident to start RIGHT NOW.
identRightNow ∷ Parser' Ident
identRightNow = do
  rawResult ← byteStringOf (skipSome identSym)
  let (result, isOp) = case BS.uncons rawResult of
        Just ('_', rest)
          | Just (rest', '_') ← BS.unsnoc rest → (rest', True)
        _ → (rawResult, False)
  guard $ not $ BS.null result
  guard $ not $ "@" `BS.isPrefixOf` result
  guard $ not $ result `elem` (["=", "in", "/", "\\/", "->", "-@>", "unpack", "fadeno", "rewrite", "true", "false"] ∷ [ByteString])
  pure (Ident result isOp)

ident ∷ Parser' Ident
ident = token identRightNow

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

data Bits = Bits8 | Bits16 | Bits32 | Bits64 | BitsInf
  deriving (Show, Eq, Ord, Lift)
data NumDesc = NumDesc !Bool {- ≥ 0 -} !Bits
  deriving (Show, Eq, Lift)

data BuiltinT
  = Tag
  | Row
  | Record
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
  | ULte
  | ULt
  | UEq
  | UNeq
  | W
  | Wrap
  | Unwrap
  | Never
  | Add !NumDesc
  | Sub !NumDesc
  | Num !NumDesc
  deriving (Show, Eq, Lift)

builtinsList ∷ Vector BuiltinT
builtinsList =
  [Tag, Row, Record, List, Bool, TypePlus, Eq, Refl, RecordGet, RecordKeepFields, RecordDropFields, ListLength, ListIndexL, NatFold, If, ULte, ULt, UEq, UNeq, W, Wrap, Unwrap, Never]
    <> (Num <$> nd)
    <> (Add <$> nd)
    <> (Sub <$> nd)
 where
  nd = NumDesc <$> [False, True] <*> [Bits8, Bits16, Bits32, Bits64, BitsInf]

identOfBuiltin ∷ BuiltinT → Ident
identOfBuiltin = \case
  Add d → r $ numDesc False d <> "_add"
  Sub d → r $ numDesc False d <> "_sub"
  Num d → r $ numDesc True d
  Tag → r "Tag"
  Bool → r "Bool"
  Row → r "Row"
  Record → r "Record"
  List → r "List"
  TypePlus → r "Type+"
  Eq → r "Eq"
  Refl → r "refl"
  RecordGet → r "record-get"
  RecordKeepFields → r "record-keep-fields"
  RecordDropFields → r "record-drop-fields"
  ListLength → r "list-length"
  ListIndexL → r "list-indexl"
  NatFold → r "nat~fold"
  If → r "if"
  ULte → o "<="
  ULt → o "<"
  UEq → o "=="
  UNeq → o "!="
  W → r "W"
  Wrap → r "wrap"
  Unwrap → r "unwrap"
  Never → r "Never"
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
  -- \| op
  o x = x `Ident` True

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

data BlockT
  = BlockLet !Quant !Ident !(Maybe TermT) !TermT !(Lambda TermT)
  | BlockRewrite !TermT !TermT
  deriving (Show, Eq, Lift)

data TermT
  = -- Term-level

    -- | Annotations only allowed on Block.
    Block !BlockT
  | Lam !Quant !Ident !(Lambda TermT)
  | App !TermT !TermT
  | AppErased !TermT !TermT
  | NumLit !Integer
  | TagLit !Ident
  | BoolLit !Bool
  | Sorry !Ident !TermT
  | Var !Int
  | ListLit !(Vector' TermT)
  | RecordLit !(Vector' (TermT, TermT))
  | -- Type-level

    -- | Cedille: Π x : T | T' / Fadeno: x : T -> T' or x : T -@> T'
    Pi !Quant !TermT !(Either (Ident, Lambda TermT) TermT)
  | Concat !TermT !(Either (Ident, Lambda TermT) TermT)
  | Builtin !BuiltinT
  | BuiltinsVar
  | ExVar !Ident !ExVarId !ExType
  | UniVar !Ident !Int !TermT
  deriving (Show, Eq, Lift)

-- | Type of existential variable.
data ExType
  = ExType !TermT -- Just a normal term.
  | ExSuperType -- "Type+ ∞", i. e. supertype of all types, i. e. ∀ u. `Type+ u : ExSuperType`
  deriving (Eq, Lift)

instance Show ExType where
  show = \case
    ExType x → show x
    ExSuperType → "Type+ ∞"

typOf ∷ TermT → TermT
typOf = App $ Builtin TypePlus

rowOf ∷ TermT → TermT
rowOf = App $ Builtin Row

recordOf ∷ TermT → TermT
recordOf = App $ Builtin Record

recordGet ∷ TermT → TermT → TermT
recordGet tag record = (Builtin RecordGet `App` tag) `App` record

typ ∷ TermT
typ = typOf $ NumLit 0

eqOf ∷ TermT → TermT → TermT
eqOf a b = (Builtin Eq) `App` a `App` b

-- If → "if"

infxr ∷ Parser' a → Parser' (a → a → a) → Parser' a
infxr a oper = do
  a' ← a
  ( do
      oper' ← oper
      oper' a' <$> infxr a oper
    )
    <|> pure a'

-- infxl ∷ Parser' a → Parser' (a → a → a) → Parser' a
-- infxl a oper = a >>= infxl'
--  where
--   infxl' prev =
--     ( do
--         oper' ← oper
--         next ← a
--         infxl' $ oper' prev next
--     )
--       <|> pure prev

sepBy ∷ Parser' () → Parser' a → Parser' [a]
sepBy with x = ((:) <$> x <*> many (with *> x)) <|> pure []

-- Syntax is *a little* ambigious. I'm very sorry.

-- Standalone '='
parseEq ∷ Parser' ()
parseEq = token $ notFollowedBy $(char '=') identSym

findVar ∷ ByteString → Parser' (Maybe (Int, Quant, Bool))
findVar name = do
  vars ← ask
  case findIndexL (\(_, Ident eName _) → eName == name) vars of
    Just n →
      let (q, Ident _ eOp) = fromMaybe (error "impossible") $ vars !? n
       in pure $ Just (n, q, eOp)
    Nothing → pure Nothing

-- 7
parsePrim ∷ Parser' TermT
parsePrim = token do
  prim ←
    (NumLit <$> number)
      <|> (TagLit <$> ($(char '.') *> ident))
      <|> (BoolLit <$> notFollowedBy ((True <$ $(string "true")) <|> (False <$ $(string "false"))) identSym)
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
              elems ← fromList <$> sepBy (token $(char '|')) (try parseTop)
              token $(char ']')
              pure (ListLit elems)
          )
      <|> (BuiltinsVar <$ (notFollowedBy $(string "fadeno") identSym))
      <|> ( Var <$> do
              -- Variable parsing
              -- TODO: { x = 4 }
              Ident iName iOp ← notFollowedBy ident parseEq
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
  accesses ← many $ $(char '.') *> (TagLit <$> identRightNow)
  pure
    $ foldl'
      (flip recordGet)
      prim
      accesses

insideEra ∷ ParserContext → ParserContext
insideEra = fmap $ first \case
  QEra → QNorm
  QNorm → QNorm

-- 6
parseApp ∷ Parser' TermT
parseApp = parsePrim >>= infxl'
 where
  infxl' prev =
    ( do
        space *> $(char '@')
        -- p ← ($(char '_') $> Nothing) <|> (Just <$> local insideEra parsePrim)
        p ← local insideEra parsePrim
        infxl' $ prev `AppErased` p
    )
      <|> ( do
              p ← parsePrim
              infxl' $ prev `App` p
          )
      <|> pure prev

-- 5
parseTy ∷ Parser' TermT
parseTy =
  ( do
      $(string "sorry/")
      n ← ident
      token $ $(char ':')
      ty ← parseTy
      pure $ Sorry n ty
  )
    <|> do
      -- Fused: parseApp <|> (->) <|> (-@>) <|> (/\)
      inNameM ← optional $ (ident <* $(char ':'))
      inTy ← parseApp
      ( ( do
            q ← token $ ($(string "->") $> QNorm) <|> ($(string "-@>") $> QEra)
            outTy ← maybe (Right <$>) (\name → fmap (Left . (name,) . Lambda) . local ((QNorm, name) <|)) inNameM parseTy
            pure $ Pi q inTy outTy
        )
          <|> ( do
                  token $ $(string "\\/")
                  rightTy ← maybe (Right <$>) (\name → fmap (Left . (name,) . Lambda) . local ((QNorm, name) <|)) inNameM parseTy
                  pure $ Concat inTy rightTy
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
    case i of
      Ident opName False →
        findVar opName >>= \case
          Just (idx, QNorm, True) → pure \a b → Var idx `App` a `App` b
          _ → empty -- Not a known operator in this scope
      _ → empty

insideLet ∷ Quant → ParserContext → ParserContext
insideLet = \case
  QEra → id
  QNorm → insideEra

-- 1
parseBlock ∷ Parser' TermT
parseBlock = do
  let
    binding = do
      ty ← optional do
        token $(string "/:")
        parseInfixOps
      q ← ($(char '@') $> QEra) <|> pure QNorm
      name ← ident
      parseEq
      expr ← local (insideLet q) $ parseTop
      pure (q, name, ty, expr)
    someEntries =
      ( do
          (q, name, ty, expr) ← binding
          rest ← Lambda <$> (local ((q, name) <|) manyEntries)
          pure $ Block $ BlockLet q name ty expr rest
      )
        <|> ( do
                -- TODO: prettyprinting
                token $ $(string "unpack")
                record ← parsePrim
                token $ $(char '.')
                fieldNames ← some (token $ notFollowedBy ident parseEq)
                foldr
                  (\name cont → Block . BlockLet QNorm name Nothing (recordGet (TagLit name) record) . Lambda <$> local ((QNorm, name) <|) cont)
                  manyEntries
                  fieldNames
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
  idents ← some ((,) <$> (($(char '@') $> QEra) <|> pure QNorm) <*> ident)
  $(char '.')
  let
    parseBod = \case
      [] → parseTop
      (x : xs) → local (x <|) $ parseBod xs
  bod ← parseBod idents
  pure $ foldr (\(q, n) → Lam q n . Lambda) bod idents

-- 0
parseTop ∷ Parser' TermT
parseTop =
  token
    $
    -- parseNode
    parseBlock
    <|> parseLam
    <|> parseInfixOps

--

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
        Sorry _ _ → ping
        Var _ → ping
        ListLit vs → ping *> traverse_ complexity vs
        RecordLit fields → ping *> traverse_ (\(k, v) → complexity k *> complexity v) fields
        Pi _ b c → ping *> complexity b *> either (complexity . unLambda . snd) complexity c
        Concat a b → complexity a *> either (complexity . unLambda . snd) complexity b
        Builtin _ → ping
        BuiltinsVar → ping
        ExVar{} → ping
        UniVar _ _ _ → ping
   in runIdentity . runEmpty (pure False) (\() → pure True) . evalState @Int 0 . complexity

pQuant ∷ Quant → Doc AnsiStyle
pQuant = \case
  QEra → "@"
  QNorm → mempty

-- TODO: Concise syntax for `\` and `-@>`
pTerm ∷ (Int, ParserContext) → TermT → Doc AnsiStyle
pTerm (oldPrec, vars) =
  withPrec oldPrec . \case
    Lam q arg x →
      ( 0
      , let sep' = case unLambda x of
              Lam _ _ _ → " "
              _
                | isSimple (unLambda x) → " "
                | otherwise → line
         in annotate (color Magenta) "\\"
              <> pQuant q
              <> pIdent arg
              <> annotate (color Magenta) "."
              <> sep'
              <> pTerm (0, (q, arg) <| vars) (unLambda x)
      )
    block@(Block{}) →
      ( 1
      , let
          go ∷ ParserContext → TermT → ([Doc AnsiStyle], TermT, ParserContext)
          go vars' = \case
            Block def → case def of
              BlockLet q name tyM val in_ →
                let entry =
                      ( maybe mempty (\ty → "/:" <+> pTerm (2, vars') ty <> line) tyM -- TODO: split if complicated type
                          <> pQuant q
                          <> pIdent name
                          <+> annotate (color Cyan) "=" <> softline <> nest 2 (pTerm (0, insideLet q vars') val)
                      )
                    (entries, rest, vars'') = go ((q, name) <| vars') $ unLambda in_
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
           in vsep entries
                <> line
                <> annotate (color Cyan) "in"
                <+> nest 2 (pTerm (1, vars'') rest)
      )
    Pi quant inTy outTy →
      ( 3
      , either (\(name, _) → pIdent name <+> ": ") mempty outTy <> pTerm (4, vars) inTy
          <+> (case quant of QNorm → "->"; QEra → "-@>")
          <+> case outTy of
            Left (name, outTy') → pTerm (3, (QNorm, name) <| vars) $ unLambda outTy'
            Right outTy' → pTerm (3, vars) outTy'
      )
    Concat a b →
      ( 3
      , case b of
          Left (n, b') → pIdent n <+> ":" <+> pTerm (4, vars) a <+> "\\/" <+> pTerm (3, (QNorm, n) <| vars) (unLambda b')
          Right b' → pTerm (4, vars) a <+> "\\/" <+> pTerm (3, vars) b'
      )
    Sorry x _ → (5, "sorry/" <> pIdent x)
    App (App (Builtin RecordGet) (TagLit tag)) rec →
      (5, pTerm (5, vars) rec <> "." <> pIdent tag)
    App lam arg2 → case lam of
      (App (Var opIdx) arg1)
        | Just (QNorm, Ident opName True) ← vars !? opIdx →
            (2, pTerm (3, vars) arg1 <+> pBS opName <+> pTerm (2, vars) arg2)
      _ →
        (4, pTerm (4, vars) lam <+> pTerm (5, vars) arg2)
    AppErased lam arg → (4, pTerm (4, vars) lam <+> "@" <> pTerm (5, vars) arg)
    Builtin x → (5, "fadeno." <> pIdent (identOfBuiltin x))
    BuiltinsVar → (5, "fadeno")
    NumLit x → (5, pretty x)
    BoolLit x → (5, if x then "true" else "false")
    TagLit x → (5, "." <> pIdent x)
    RecordLit fields →
      ( 5
      , encloseSep
          (annotate (color White) "{")
          (annotate (color White) "}")
          (annotate (color White) " | ")
          (fmap (\(n, v) → pTerm (5, vars) n <+> annotate (color Cyan) "=" <+> pTerm (0, vars) v) (toList fields))
      )
    ListLit vec → (5, encloseSep "[" "]" " | " $ fmap (\x → pTerm (0, vars) x) (toList vec))
    Var x → (5, maybe ("#" <> pretty x) (\(q, i) → pQuant q <> pIdent i) $ vars !? x)
    -- RecordGet a b -> case b of
    --   TagLit b' -> (6, pTerm 6 a <> "." <> pIdent b')
    --   _ -> (5, "fadeno/get" <+> pTerm 6 a <+> pTerm 6 b)
    ExVar n l t → (5, "(exi#" <> pretty (show l) <+> pIdent n <+> ":" <+> pExType (0, vars) t <> ")")
    UniVar x' l t → (5, "(uni#" <> pretty l <+> pIdent x' <+> ":" <+> pTerm (0, vars) t <> ")")

pTerm' ∷ TermT → Doc AnsiStyle
pTerm' = pTerm (0, [])

pExType ∷ (Int, ParserContext) → ExType → Doc AnsiStyle
pExType a = \case
  ExType x → pTerm a x
  ExSuperType → "Type+ ∞"

parse ∷ ParserContext → ByteString → Either Text TermT
parse vars inp = case runParser (parseTop <* eof) vars 0 inp of
  OK x _ "" → Right x
  Err e → Left $ "Unable to parse at " <> tshow (posLineCols inp [e])
  _ → Left "Internal error: uncaught failure"

parseFile ∷ FilePath → IO TermT
parseFile x = either (error . show) id . parse [] <$> readFileBinary x

render ∷ Doc AnsiStyle → IO ()
render x = renderIO stdout $ layoutSmart defaultLayoutOptions $ x <> line

formatFile ∷ FilePath → IO ()
formatFile = render . pTerm' <=< parseFile
