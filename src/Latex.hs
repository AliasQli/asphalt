{-# LANGUAGE FlexibleInstances #-}

module Latex where
import ADT
import Data.List (intercalate)

class ShowLatex a where
  showsLatexPrec :: Int -> a -> ShowS
  showLatex :: a -> String
  showsLatexPrec _ x s = showLatex x ++ s
  showLatex x          = showsLatexPrec 0 x ""
  {-# MINIMAL showsLatexPrec | showLatex #-}

instance ShowLatex Type where
  showsLatexPrec _ One = showString "\\bold{1}"
  showsLatexPrec _ Zero = showString "\\bold{0}"
  showsLatexPrec d (t1 :->: t2) = showParen (d > 5) $ showsLatexPrec 6 t1 . showString " \\multimap " . showsLatexPrec 5 t2
  showsLatexPrec d (t1 :*: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\otimes " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :+: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\oplus " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :&: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\& " . showsLatexPrec 7 t2

instance ShowLatex ADT where
  showsLatexPrec d (Lam v t e) = showParen (d > 1) $
    showString "\\lambda (" . showString v . showString " : " . showsLatexPrec 0 t . showString "). \\space " . showsLatexPrec 0 e
  showsLatexPrec d (App e1 e2) = showParen (d > 10) $
    showsLatexPrec 10 e1 . showString " \\space " . showsLatexPrec 11 e2
  showsLatexPrec _ (Var v) = showString v
  showsLatexPrec d (Tensor e1 e2) = showParen (d > 4) $
    showsLatexPrec 5 e1 . showString " \\otimes " . showsLatexPrec 5 e2
  showsLatexPrec d (LetTensor v1 v2 e1 e2) = showParen (d > 1) $
    showString "\\text{let } " . showString v1 . showString " \\otimees " . showString v2 . showString " = " . showsLatexPrec 0 e1 .
    showString " \\text{ in } " . showsLatexPrec 0 e2
  showsLatexPrec _ Star = showString "*"
  showsLatexPrec d (Inl ty e1) = showParen (d > 10) $
    showString "\\text{inl} ^{" . showsPrec 11 ty . showString "} \\space " . showsLatexPrec 11 e1
  showsLatexPrec d (Inr ty e1) = showParen (d > 10) $
    showString "\\text{inr} ^{" . showsPrec 11 ty . showString "} \\space "  . showsLatexPrec 11 e1
  showsLatexPrec d (CasePlus e1 v1 e2 v2 e3) = showParen (d > 0) $
    showString "\\text{case } " . showsLatexPrec 11 e1 . showString " \\text{ of \
    \inl } " . showString v1 . showString " \\to " . showsLatexPrec 1 e2 . showString "\\text{; \
    \inr } " . showString v2 . showString " \\to " . showsLatexPrec 0 e3
  showsLatexPrec d (Absurd ty e1) = showParen (d > 10) $
    showString "\\text{absurd} ^{" . showsPrec 11 ty . showString "} \\space " . showsLatexPrec 11 e1
  showsLatexPrec d (With e1 e2) = showParen (d > 4) $
    showsLatexPrec 5 e1 . showString " \\& " . showsLatexPrec 5 e2
  showsLatexPrec d (Fst e1) = showParen (d > 10) $
    showString "\\text{fst } " . showsLatexPrec 11 e1
  showsLatexPrec d (Snd e1) = showParen (d > 10) $
    showString "\\text{snd } " . showsLatexPrec 11 e1

instance ShowLatex Context where
  showLatex = go []
    where
      underline v vs = if v `elem` vs
        then \x -> "\\underline{" ++ x ++ "}"
        else id
      go _ [] = "\\cdot"
      go vs [(v, _, t)] = underline v vs $ v ++ " : " ++ showLatex t
      go vs ((v, _, t) : ctx) = underline v vs $ go (v:vs) ctx ++ ", " ++ v ++ " : " ++ showLatex t

showLatexContextSimple :: Context -> String
showLatexContextSimple [] = "\\cdot"
showLatexContextSimple [(v, _, _)] = v
showLatexContextSimple ((v, _, _) : ctx) = showLatexContextSimple ctx ++ ", " ++ v

data By
  = LolipopI | LolipopE
  | TensorI  | TensorE
  | OneI
  | PlusIL   | PlusIR  | PlusE
  | ZeroE
  | WithI    | WithEL  | WithER
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
  showLatex Nil = ""

data Judgement
  = Judgement
    { inc  :: Context
    , out  :: Context
    , expr :: ADT
    , ty   :: Type
    }

instance Show Judgement where
  show (Judgement inc out expr ty) = show inc ++ " \\ " ++ show out ++ " |- " ++ show expr ++ " : " ++ show ty

instance ShowLatex Judgement where
  showLatex (Judgement inc out expr ty) =
    showLatex inc ++ " \\backslash " ++ showLatexContextSimple out ++ " \\vdash " ++ showLatex expr ++ " : " ++ showLatex ty

data Latex = Latex [Latex] Judgement By

instance Show Latex where
  show (Latex l j by) = "\\displaystyle \\frac {" ++ intercalate "\\qquad" (show <$> l) ++ "} {" ++ showLatex j ++ "} " ++ showLatex by
