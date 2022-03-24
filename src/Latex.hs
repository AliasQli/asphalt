{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Latex where
import Data.Text (Text)
import qualified Data.Text.IO as T
import qualified Data.Text as T
type TextS = Text -> Text

class ShowText a where
  textPrec :: Int -> a -> TextS
  text :: a -> Text
  textPrec _ x s = text x <> s
  text x = textPrec 0 x ""

printText :: ShowText a => a -> IO ()
printText = T.putStrLn . text

showText :: Text -> TextS
showText = (<>)

showTextParen :: Bool -> TextS -> TextS
showTextParen b p   =  if b then showText "(" . p . showText ")" else p

class ShowLatex a where
  showsLatexPrec :: Int -> a -> TextS
  showLatex      :: a -> Text
  showsLatexPrec _ x s = showLatex x <> s
  showLatex x          = showsLatexPrec 0 x ""
  {-# MINIMAL showsLatexPrec | showLatex #-}

data By
  = LolipopI | LolipopE
  | TensorI  | TensorE
  | OneI
  | PlusIL   | PlusIR  | PlusE
  | ZeroE
  | WithI    | WithEL  | WithER
  | MuI      | MuE
  | ByFix
  | Nil
  deriving (Eq, Ord)

instance ShowText By where
  text LolipopI = "⊗I"
  text LolipopE = "⊗E"
  text TensorI = "⊗I"
  text TensorE = "⊗E"
  text OneI = "1I"
  text PlusIL = "⊕IL"
  text PlusIR = "⊕IR"
  text PlusE = "⊕E"
  text ZeroE = "0E"
  text WithI = "&I"
  text WithEL = "&EL"
  text WithER = "&ER"
  text MuI = "μI"
  text MuE = "μE"
  text ByFix = "fix"
  text Nil = ""

instance ShowLatex By where
  showLatex LolipopI = "\\multimap \\text{I}"
  showLatex LolipopE = "\\multimap \\text{E}"
  showLatex TensorI = "\\otimes \\text{I}"
  showLatex TensorE = "\\otimes \\text{E}"
  showLatex OneI = "\\bold{1} \\text{I}"
  showLatex PlusIL = "\\oplus \\text{I}_L"
  showLatex PlusIR = "\\oplus \\text{I}_R"
  showLatex PlusE = "\\oplus \\text{E}"
  showLatex ZeroE = "\\bold{0} \\text{E}"
  showLatex WithI = "\\& \\text{I}"
  showLatex WithEL = "\\& \\text{E}_L"
  showLatex WithER = "\\& \\text{E}_R"
  showLatex MuI = "\\mu \\text{I}"
  showLatex MuE = "\\mu \\text{E}"
  showLatex ByFix = "\\text{fix}"
  showLatex Nil = ""

instance ShowText Integer where
  text = T.pack . show