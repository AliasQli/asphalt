{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module AST (module AST, module Type) where

import Data.List (intercalate)

import Latex
import Type

data AST
  = Lam Var Type AST              -- λ (Var : Type). AST
  | App AST AST                   -- AST AST
  | Var Var                       -- Var
  | Call Name                     -- Name
  | Tensor AST AST                -- AST * AST
  | LetTensor Var Var AST AST     -- let Var * Var = AST in AST
  | Star                          -- *
  | Inl Type AST                  -- inl Type AST
  | Inr Type AST                  -- inr Type AST
  | CasePlus AST Var AST Var AST  -- case AST of inl Var -> AST; inr Var -> AST
  | Absurd Type AST               -- absurd Type AST
  | With AST AST                  -- AST & AST
  | Fst AST                       -- fst AST
  | Snd AST                       -- snd AST
  | Fold Type AST                 -- fold Type AST
  | Unfold AST                    -- unfold AST
  | Fix Var Type AST              -- fix (Var : Type). AST

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

type Serial = Integer

type Context = [(Var, Integer, Type)]

instance {-# Overlapping #-} Show Context where
  show [] = "⋅"
  show [(v, _, t)] = v <> " : " <> show t
  show ((v, _, t) : ctx) = show ctx <> ", " <> v <> " : " <> show t

instance ShowLatex Context where
  showLatex = go []
    where
      underline v vs = if v `elem` vs
        then \x -> "\\underline{" <> x <> "}"
        else id
      go _ [] = "\\cdot"
      go vs [(v, _, t)] = underline v vs $ v <> " : " <> showLatex t
      go vs ((v, _, t) : ctx) = underline v vs $ go (v:vs) ctx <> ", " <> v <> " : " <> showLatex t

showLatexContextSimple :: Context -> String
showLatexContextSimple [] = "\\cdot"
showLatexContextSimple [(v, _, _)] = v
showLatexContextSimple ((v, _, _) : ctx) = showLatexContextSimple ctx <> ", " <> v

data Decl
  = TypeDecl Name Type
  | TermDecl Name AST

instance Show Decl where
  show (TypeDecl v ty) = "type " <> v <> " = " <> show ty
  show (TermDecl v e) = v <> " = " <> show e

type Source = [Decl]

instance {-# Overlapping #-} Show Source where
  show decls = unlines (show <$> decls)

type Typing = (Var, Type)

instance {-# Overlapping #-} Show Typing where
  show (name, ty) = name <> " : " <> show ty

instance ShowLatex Typing where
  showLatex (name, ty) = "\\text{" <> name <> "} : " <> showLatex ty

data Prototype
  = TypeProto Synonym
  | TermProto Typing

instance Show Prototype where
  show (TypeProto syn) = show syn
  show (TermProto typing) = show typing

type Interface = [Prototype]

instance {-# Overlapping #-} Show Interface where
  show protos = unlines (show <$> protos)

data Judgement
  = Judgement
    { inc  :: Context
    , out  :: Context
    , expr :: AST
    , ty   :: Type
    }

instance Show Judgement where
  show (Judgement inc out expr ty) = show inc <> " \\ " <> show out <> " |- " <> show expr <> " : " <> show ty

instance ShowLatex Judgement where
  showLatex (Judgement inc out expr ty) =
    showLatex inc <> " \\backslash " <> showLatexContextSimple out <> " \\vdash " <> showLatex expr <> " : " <> showLatex ty

data Frac
  = Frac [Frac] Judgement By
  | FracIntro Typing Judgement

instance ShowLatex Frac where
  showLatex (Frac l j by) = "\\displaystyle \\frac {" <> intercalate "\\qquad" (showLatex <$> l) <> "} {" <> showLatex j <> "} " <> showLatex by
  showLatex (FracIntro typing j) = "\\displaystyle \\frac {" <> showLatex typing <> "} {" <> showLatex j <> "} \\text{intro}"

data Latex
  = LatexFrac Frac
  | LatexSynonym Synonym

instance ShowLatex Latex where
  showLatex (LatexFrac frac) = showLatex frac
  showLatex (LatexSynonym syn) = showLatex syn

instance {-# Overlapping #-} Show [Latex] where
  show = unlines . fmap ((<> " \\newline") . showLatex)
