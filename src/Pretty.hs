module Pretty where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.List qualified as List

class Pretty a where
    prettyPrec :: Int -> a -> String
    pretty :: a -> String
    prettyPrec _ = pretty
    pretty = prettyPrec 0

class PrettyVar a where
    prettyVar :: Int -> a -> String
    prettyVarStrip :: a -> String

instance PrettyVar String where
    prettyVar _ = id
    prettyVarStrip = id

instance {-# OVERLAPPABLE #-} (PrettyVar a, Pretty b) => PrettyVar (a, b) where
    prettyVar p (n, t) = parensIf (p > 0) $ prettyVar 0 n <> ": " <> pretty t
    prettyVarStrip (n, _) = prettyVarStrip n

instance {-# OVERLAPPABLE #-} Show a => Pretty a where
    pretty = show

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty (a, b) = "(" <> pretty a <> ", " <> pretty b <> ")"

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
    pretty (a, b, c) = "(" <> pretty a <> ", " <> pretty b <> ", " <> pretty c <> ")"

instance Pretty a => Pretty [a] where
    pretty = brackets . List.intercalate ", " . fmap pretty

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b) => Pretty (Map a b) where
    pretty = braces . List.intercalate ", " . fmap (\(a, b) -> pretty a <> " = " <> pretty b) . Map.toList

instance Pretty b => Pretty (Either String b) where
    prettyPrec p = either id (prettyPrec p)

instance Pretty a => Pretty (Maybe a) where
    prettyPrec p = maybe "" (prettyPrec p)




parensIf :: Bool -> String -> String
parensIf True = parens
parensIf False = id

parens :: String -> String
parens s = "(" <> s <> ")"

brackets :: String -> String
brackets s = "[" <> s <> "]"

braces :: String -> String
braces s = "{" <> s <> "}"

angles :: String -> String
angles s = "<" <> s <> ">"
