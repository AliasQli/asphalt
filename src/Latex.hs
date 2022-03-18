{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Latex where

import AST
import Data.List (intercalate)

class ShowLatex a where
  showsLatexPrec :: Int -> a -> ShowS
  showLatex      :: a -> String
  showsLatexPrec _ x s = showLatex x ++ s
  showLatex x          = showsLatexPrec 0 x ""
  {-# MINIMAL showsLatexPrec | showLatex #-}

instance Show Kind where
  showsPrec _ Type = showString "*"
  showsPrec d (a :->> b) = showParen (d > 5) $ showsPrec 6 a . showString " -> " . showsPrec 5 b

instance ShowLatex Kind where
  showsLatexPrec _ Type = showString "*"
  showsLatexPrec d (a :->> b) = showParen (d > 5) $ showsLatexPrec 6 a . showString " \\to " . showsLatexPrec 5 b

instance Show Type where
  showsPrec _ One = showString "1"
  showsPrec _ Zero = showString "0"
  showsPrec d (t1 :->: t2) = showParen (d > 5) $ showsPrec 6 t1 . showString " ⊸ " . showsPrec 5 t2
  showsPrec d (t1 :*: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " ⊗ " . showsPrec 7 t2
  showsPrec d (t1 :+: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " ⊕ " . showsPrec 7 t2
  showsPrec d (t1 :&: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " & " . showsPrec 7 t2
  showsPrec _ (TypeVar v) = showString v
  showsPrec d (Mu v t) = showParen (d > 1) $ showString "μ " . showString v . showString ". " . showsPrec 1 t
  showsPrec d (t1 :.: t2) = showParen (d > 10) $ showsPrec 10 t1 . showString " " . showsPrec 11 t2
  showsPrec d (TypeLam v k t2) = showParen (d > 1) $ showString "λ (" . showString v . showString " : " . shows k . showString "). " . shows t2

instance ShowLatex Type where
  showsLatexPrec _ One = showString "\\bold{1}"
  showsLatexPrec _ Zero = showString "\\bold{0}"
  showsLatexPrec d (t1 :->: t2) = showParen (d > 5) $ showsLatexPrec 6 t1 . showString " \\multimap " . showsLatexPrec 5 t2
  showsLatexPrec d (t1 :*: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\otimes " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :+: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\oplus " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :&: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\& " . showsLatexPrec 7 t2
  showsLatexPrec _ (TypeVar v) = showString v
  showsLatexPrec d (Mu v t) = showParen (d > 1) $ showString "\\mu " . showString v . showString " . \\space " . showsLatexPrec 1 t
  showsLatexPrec d (t1 :.: t2) = showParen (d > 10) $ showsLatexPrec 10 t1 . showString " \\space " . showsLatexPrec 11 t2
  showsLatexPrec d (TypeLam v k t2) = showParen (d > 1) $ showString "\\lambda (" . showString v . showString  ":" . showsLatexPrec 0 k . showString " . \\space " . showsLatexPrec 1 t2

instance Show AST where
  showsPrec d (Lam v t e) = showParen (d > 1) $
    showString "λ (" . showString v . showString " : " . shows t . showString "). " . shows e
  showsPrec d (App e1 e2) = showParen (d > 10) $
    showsPrec 10 e1 . showString " " . showsPrec 11 e2
  showsPrec _ (Var v) = showString v
  showsPrec _ (Call c) = showString c
  showsPrec d (Tensor e1 e2) = showParen (d > 4) $
    showsPrec 5 e1 . showString " ⊗ " . showsPrec 5 e2
  showsPrec d (LetTensor v1 v2 e1 e2) = showParen (d > 1) $
    showString "let " . showString v1 . showString " ⊗ " . showString v2 . showString " = " . shows e1 . showString " in " . shows e2
  showsPrec _ Star = showString "*"
  showsPrec d (Inl ty e1) = showParen (d > 10) $
    showString "inl " . showsPrec 11 ty . showString " " . showsPrec 11 e1
  showsPrec d (Inr ty e1) = showParen (d > 10) $
    showString "inr " . showsPrec 11 ty . showString " " . showsPrec 11 e1
  showsPrec d (CasePlus e1 v1 e2 v2 e3) = showParen (d > 0) $
    showString "case " . showsPrec 3 e1 . showString " of \
    \inl " . showString v1 . showString " -> " . showsPrec 1 e2 . showString "; \
    \inr " . showString v2 . showString " -> " . showsPrec 1 e3
  showsPrec d (Absurd ty e1) = showParen (d > 10) $
    showString "absurd " . showsPrec 11 ty . showString " " . showsPrec 11 e1
  showsPrec d (With e1 e2) = showParen (d > 4) $
    showsPrec 5 e1 . showString " & " . showsPrec 5 e2
  showsPrec d (Fst e1) = showParen (d > 10) $
    showString "fst " . showsPrec 11 e1
  showsPrec d (Snd e1) = showParen (d > 10) $
    showString "snd " . showsPrec 11 e1
  showsPrec d (Fold ty body) = showParen (d > 10) $
    showString "fold " . showsPrec 11 ty . showString " " . showsPrec 11 body
  showsPrec d (Unfold body) = showParen (d > 10) $
    showString "unfold " . showsPrec 11 body
  showsPrec d (Fix v ty body) = showParen (d > 1) $
    showString "fix (" . showString v . showString " : " . shows ty . showString "). " . shows body

instance ShowLatex AST where
  showsLatexPrec d (Lam v t e) = showParen (d > 1) $
    showString "\\lambda (" . showString v . showString " : " . showsLatexPrec 0 t . showString "). \\space " . showsLatexPrec 0 e
  showsLatexPrec d (App e1 e2) = showParen (d > 10) $
    showsLatexPrec 10 e1 . showString " \\space " . showsLatexPrec 11 e2
  showsLatexPrec _ (Var v) = showString v
  showsLatexPrec _ (Call c) = showString "\\text{" . showString c . showString "}"
  showsLatexPrec d (Tensor e1 e2) = showParen (d > 4) $
    showsLatexPrec 5 e1 . showString " \\otimes " . showsLatexPrec 5 e2
  showsLatexPrec d (LetTensor v1 v2 e1 e2) = showParen (d > 1) $
    showString "\\text{let } " . showString v1 . showString " \\otimes " . showString v2 . showString " = " . showsLatexPrec 0 e1 .
    showString " \\text{ in } " . showsLatexPrec 0 e2
  showsLatexPrec _ Star = showString "*"
  showsLatexPrec d (Inl ty e1) = showParen (d > 10) $
    showString "\\text{inl} ^{" . showsPrec 11 ty . showString "} \\space " . showsLatexPrec 11 e1
  showsLatexPrec d (Inr ty e1) = showParen (d > 10) $
    showString "\\text{inr} ^{" . showsPrec 11 ty . showString "} \\space "  . showsLatexPrec 11 e1
  showsLatexPrec d (CasePlus e1 v1 e2 v2 e3) = showParen (d > 0) $
    showString "\\text{case } " . showsLatexPrec 3 e1 . showString " \\text{ of \
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
  showsLatexPrec d (Fold ty body) = showParen (d > 10) $
    showString "\\text{fold} ^{" . showsPrec 11 ty . showString "} \\space " . showsLatexPrec 11 body
  showsLatexPrec d (Unfold body) = showParen (d > 10) $
    showString "\\text{unfold } " . showsLatexPrec 11 body
  showsLatexPrec d (Fix v ty body) = showParen (d > 1) $
    showString "\\text{fix } (" . showString v . showString " : " . showsLatexPrec 0 ty . showString "). \\space  " . showsLatexPrec 0 body

instance {-# Overlapping #-} Show Context where
  show [] = "⋅"
  show [(v, _, t)] = v ++ " : " ++ show t
  show ((v, _, t) : ctx) = show ctx ++ ", " ++ v ++ " : " ++ show t

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
  | MuI      | MuE
  | ByFix
  | Intro
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
  show Intro = "intro"
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
  showLatex Intro = "\\text{intro}"
  showLatex Nil = ""

data Judgement
  = Judgement
    { inc  :: Context
    , out  :: Context
    , expr :: AST
    , ty   :: Type
    }

instance Show Judgement where
  show (Judgement inc out expr ty) = show inc ++ " \\ " ++ show out ++ " |- " ++ show expr ++ " : " ++ show ty

instance ShowLatex Judgement where
  showLatex (Judgement inc out expr ty) =
    showLatex inc ++ " \\backslash " ++ showLatexContextSimple out ++ " \\vdash " ++ showLatex expr ++ " : " ++ showLatex ty

data Typing
  = Typing
    { name :: Var
    , ty   :: Type
    }

instance Show Typing where
  show (Typing name ty) = name ++ " : " ++ show ty

instance ShowLatex Typing where
  showLatex (Typing name ty) = "\\text{" ++ name ++ "} : " ++ showLatex ty

data Latex = Latex (Either [Latex] Typing) Judgement By

latex :: [Latex] -> Judgement -> By -> Latex
latex ls = Latex (Left ls)

instance ShowLatex Latex where
  showLatex (Latex (Left l) j by) = "\\displaystyle \\frac {" ++ intercalate "\\qquad" (showLatex <$> l) ++ "} {" ++ showLatex j ++ "} " ++ showLatex by
  showLatex (Latex (Right typing) j by) = "\\displaystyle \\frac {" ++ showLatex typing ++ "} {" ++ showLatex j ++ "} " ++ showLatex by

data Synonym
  = Synonym
    { name :: Var
    , nf   :: Type
    , kind :: Kind
    }

instance Show Synonym where
  show (Synonym name nf kind) = "type " ++ name ++ " => " ++ show nf ++ " : " ++ show kind

instance ShowLatex Synonym where
  showLatex (Synonym name nf kind) = "\\text{type } " ++ name ++ " \\hookrightarrow " ++ showLatex nf ++ " : " ++ showLatex kind

instance Show Decl where
  show (TypeDecl v ty) = "type " ++ v ++ " = " ++ show ty
  show (TermDecl v e) = v ++ " = " ++ show e

instance {-# Overlapping #-} Show Source where
  show decls = unlines (show <$> decls)
