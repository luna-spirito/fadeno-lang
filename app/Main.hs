module Main where

import RIO
import qualified RIO.Text as T
import Parser
import Lexer (Ident(..))

-- render :: ExprT → Text
-- render = render' 0 where
--   renderIndent indent = T.replicate indent " "
  
--   renderLams indent = \case
--     Lam var expr → " \"" <> tshow var <> renderLams expr
--     e → render' (indent + 1) e

--   render' indent = \case
--     Lam var expr → renderIndent indent <> "\"" <> tshow var <> renderLams indent expr
--     Let defs final →
--       mconcat (defs <&> \(name, val) → renderIndent indent <> "let " <> tshow name <> " =\n" <> render' (indent + 1) val <> "\n")
--       <> renderIndent indent <> "in\n" <> render' (indent + 1) final
--     Op a
render :: ExprT → Text
render = \case
  Lam (Ident name) x → "(\\" <> decodeUtf8Lenient name <> " " <> render x <> ")"
  Let defs final → "(" <> mconcat (defs <&> \(Ident name, val) → "let " <> decodeUtf8Lenient name <> " = " <> render val) <> " in " <> render final <> ")"
  Op  a x b → "(" <> render a <> " " <> tshow x <> " " <> render b <> ")"
  App a b → "(" <> render a <> " " <> render b <> ")"
  Nat x → tshow x
  Var (Ident x) → decodeUtf8Lenient x




-- newtype WireId- = WireId Word32

-- data Wire = Wire ! 


main :: IO ()
main = pure ()
