{-# LANGUAGE FlexibleInstances #-}

module Latex where

class ShowLatex a where
  showsLatexPrec :: Int -> a -> ShowS
  showLatex      :: a -> String
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

instance Show By where
  show LolipopI = "⊗I"
  show LolipopE = "⊗E"
  show TensorI = "⊗I"
  show TensorE = "⊗E"
  show OneI = "1I"
  show PlusIL = "⊕IL"
  show PlusIR = "⊕IR"
  show PlusE = "⊕E"
  show ZeroE = "0E"
  show WithI = "&I"
  show WithEL = "&EL"
  show WithER = "&ER"
  show MuI = "μI"
  show MuE = "μE"
  show ByFix = "fix"
  show Nil = ""

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
