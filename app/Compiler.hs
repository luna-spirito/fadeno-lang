-- This is for
module Compiler () where

import Control.Algebra
import Control.Carrier.State.Church (State, get, put)
import Control.Carrier.Writer.Church (Writer, execWriter, tell)
import Data.IntSet (maxView, member)
import Data.RRBVector (Vector, imap, replicate, splitAt, (<|))
import Normalize (rewrite)
import Parser (BlockT (..), BuiltinT (..), Ident, Lambda (..), Quant (..), TermT (..), Vector' (..), intercept)
import RIO hiding (Vector, replicate)
import RIO.HashMap qualified as HM

-- Unfortunately, not a rewrite', since this just erases & is not meant to
-- simplify anything
erase ∷ Vector Bool → TermT → TermT
erase reals = \case
  NumLit x → NumLit x
  TagLit tag → TagLit tag
  BoolLit x → BoolLit x
  ListLit entries → ListLit $ erase reals <$> entries
  RecordLit fields → RecordLit $ bimap (erase reals) (erase reals) <$> fields
  Lam QNorm n body → Lam QNorm n $ Lambda $ erase (True <| reals) $ unLambda body
  Lam QEra _ body → erase (False <| reals) $ unLambda body
  App f a → App (erase reals f) (erase reals a)
  AppErased f _a → erase reals f
  Var x →
    let (potentiallyErased, _) = splitAt x reals
     in Var $ x - foldl' (\acc real → if real then acc else acc + 1) 0 potentiallyErased
  BuiltinsVar → BuiltinsVar
  Builtin x → Builtin x
  Block (BlockLet QNorm n _ty val body) → Block $ BlockLet QNorm n Nothing val $ Lambda $ erase (True <| reals) $ unLambda body
  Block (BlockLet QEra _ _ _ body) → erase (False <| reals) $ unLambda body
  Block (BlockRewrite _ body) → erase reals body
  Sorry → Sorry
  Pi q inT outT → Pi q (erase reals inT) (either (Left . fmap \bod → Lambda $ erase (True <| reals) $ unLambda bod) (Right . erase reals) outT)
  Concat aT bT → Concat (erase reals aT) (either (Left . fmap \bod → Lambda $ erase (True <| reals) $ unLambda bod) (Right . erase reals) bT)
  ExVar{} → undefined
  UniVar{} → undefined

listCaptures ∷ Lambda TermT → IntSet
listCaptures =
  runIdentity
    . execWriter
    . rewrite
      (\_ → (+ 1))
      (+ 1)
      ( \t locals →
          Nothing <$ case t of
            Var x → if x >= locals then tell @IntSet [x - locals] else pure ()
            _ → pure ()
      )
      1 -- Local bindings
    . unLambda

-- Identifies captured bindings and erases non-captured variables
lambdaToClosure ∷ Lambda TermT → (IntSet, Lambda TermT)
lambdaToClosure orig =
  let
    captures = listCaptures orig
    reals = imap (\i () → i `member` captures) (replicate (maybe 0 fst $ maxView captures) ())
   in
    (captures, Lambda $ erase (True <| reals) $ unLambda orig)

data Value
  = VNum !Integer
  | VTag !Int64
  | VBool !Bool
  | VList !(Vector Value)
  | VRecord !Int !(Vector Value)
  | VLam !(Vector Value) !(Vector Instr)
  | VBuiltinsVar
  | VBuiltin !BuiltinT
  | VPanic
  deriving
    ( -- | Pi !Quant !TermT !(Either (Ident, Lambda TermT) TermT)
      -- | Concat !TermT !(Either (Ident, Lambda TermT) TermT)
      Show
    , Eq
    )

{-
Basically, all the instruction set is just a "flat" sequence of operations that builds a tree.
All intermediate values are pushed on the stack.
It also has bindings (registers) that it can refer to.
-}
data Instr
  = IPush !Value
  | IMkVar
  | ICopyVar !Word16
  | ITakeVar !Word16
  | IApp
  | IClosure !IntSet !(Vector Instr) -- IntSet stands for captured variables
  | IIfElse !(Vector Instr) !(Vector Instr) -- Flattened to IIf and IElse
  | IMkList !Word16
  -- IArg as optimization?
  deriving (Show, Eq)

type Compile = State (HashMap Ident Int64) :+: Writer (Vector Instr)

instr ∷ (Has Compile sig m) ⇒ Instr → m ()
instr x = tell @(Vector Instr) [x]

-- compiles erased
compile' ∷ (Has Compile sig m) ⇒ TermT → m ()
compile' = \case
  NumLit x → instr $ IPush $ VNum x
  TagLit tag →
    instr . IPush . VTag =<< do
      toI ← get @(HashMap Ident Int64)
      case HM.lookup tag toI of
        Just i → pure i
        Nothing → do
          let i = fromIntegral $ HM.size toI
          put $ HM.insert tag i toI
          pure i
  BoolLit x → instr $ IPush $ VBool x
  ListLit (Vector' entries) → do
    for_ entries compile'
    instr $ IMkList $ fromIntegral $ length entries
  RecordLit _ → error "TODO"
  Lam QNorm _ body → do
    let (captures, body') = lambdaToClosure body
    (body'', ()) ← intercept @(Vector Instr) $ compile' $ unLambda body'
    instr $ IClosure captures body''
  Lam QEra _ _ → undefined
  (Builtin If `App` b `App` t `App` f) → do
    compile' b
    (t', ()) ← intercept @(Vector Instr) $ compile' t
    (f', ()) ← intercept @(Vector Instr) $ compile' f
    instr $ IIfElse t' f'
  App f a → do
    compile' f
    compile' a
    instr IApp
  AppErased{} → undefined
  Var x → instr $ ICopyVar $ fromIntegral x
  BuiltinsVar → instr $ IPush VBuiltinsVar
  Builtin x → instr $ IPush $ VBuiltin x
  Block (BlockLet QNorm _n _ty val body) → do
    compile' val
    instr IMkVar
    compile' $ unLambda body
  Block (BlockLet QEra _ _ _ body) → undefined
  Block (BlockRewrite _ body) → undefined
  Sorry → instr $ IPush VPanic
  Pi q inT outT → error "TODO"
  Concat aT bT → error "TODO"
  ExVar{} → undefined
  UniVar{} → undefined
