module Main where

import RIO
import qualified RIO.Text as T
import Parser

render :: ExprT → Text
render = \case
  Lam (Ident name) x → "(\\" <> decodeUtf8Lenient name <> " " <> render x <> ")"
  Let defs final → "(" <> mconcat (defs <&> \(Ident name, val) → "let " <> decodeUtf8Lenient name <> " = " <> render val) <> " in " <> render final <> ")"
  Op  a x b → "(" <> render a <> " " <> tshow x <> " " <> render b <> ")"
  App a b → "(" <> render a <> " " <> render b <> ")"
  Nat x → tshow x
  Var (Ident x) → decodeUtf8Lenient x

main :: IO ()
main = pure ()
