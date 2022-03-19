{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module AST (module AST, module Type) where

import Data.Text (Text)
import qualified Data.Text as T

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
  deriving Show

instance ShowText AST where
  textPrec d (Lam v t e) = showTextParen (d > 1) $
    showText "λ (" . showText v . showText " : " . textPrec 0 t . showText "). " . textPrec 0 e
  textPrec d (App e1 e2) = showTextParen (d > 10) $
    textPrec 10 e1 . showText " " . textPrec 11 e2
  textPrec _ (Var v) = showText v
  textPrec _ (Call c) = showText c
  textPrec d (Tensor e1 e2) = showTextParen (d > 4) $
    textPrec 5 e1 . showText " ⊗ " . textPrec 5 e2
  textPrec d (LetTensor v1 v2 e1 e2) = showTextParen (d > 1) $
    showText "let " . showText v1 . showText " ⊗ " . showText v2 . showText " = " . textPrec 0 e1 . showText " in " . textPrec 0 e2
  textPrec _ Star = showText "*"
  textPrec d (Inl ty e1) = showTextParen (d > 10) $
    showText "inl " . textPrec 11 ty . showText " " . textPrec 11 e1
  textPrec d (Inr ty e1) = showTextParen (d > 10) $
    showText "inr " . textPrec 11 ty . showText " " . textPrec 11 e1
  textPrec d (CasePlus e1 v1 e2 v2 e3) = showTextParen (d > 0) $
    showText "case " . textPrec 3 e1 . showText " of \
    \inl " . showText v1 . showText " -> " . textPrec 1 e2 . showText "; \
    \inr " . showText v2 . showText " -> " . textPrec 1 e3
  textPrec d (Absurd ty e1) = showTextParen (d > 10) $
    showText "absurd " . textPrec 11 ty . showText " " . textPrec 11 e1
  textPrec d (With e1 e2) = showTextParen (d > 4) $
    textPrec 5 e1 . showText " & " . textPrec 5 e2
  textPrec d (Fst e1) = showTextParen (d > 10) $
    showText "fst " . textPrec 11 e1
  textPrec d (Snd e1) = showTextParen (d > 10) $
    showText "snd " . textPrec 11 e1
  textPrec d (Fold ty body) = showTextParen (d > 10) $
    showText "fold " . textPrec 11 ty . showText " " . textPrec 11 body
  textPrec d (Unfold body) = showTextParen (d > 10) $
    showText "unfold " . textPrec 11 body
  textPrec d (Fix v ty body) = showTextParen (d > 1) $
    showText "fix (" . showText v . showText " : " . textPrec 0 ty . showText "). " . textPrec 0 body

-- instance Show AST where
--   show = T.unpack . text

instance ShowLatex AST where
  showsLatexPrec d (Lam v t e) = showTextParen (d > 1) $
    showText "\\lambda (" . showText v . showText " : " . showsLatexPrec 0 t . showText "). \\space " . showsLatexPrec 0 e
  showsLatexPrec d (App e1 e2) = showTextParen (d > 10) $
    showsLatexPrec 10 e1 . showText " \\space " . showsLatexPrec 11 e2
  showsLatexPrec _ (Var v) = showText v
  showsLatexPrec _ (Call c) = showText "\\text{" . showText c . showText "}"
  showsLatexPrec d (Tensor e1 e2) = showTextParen (d > 4) $
    showsLatexPrec 5 e1 . showText " \\otimes " . showsLatexPrec 5 e2
  showsLatexPrec d (LetTensor v1 v2 e1 e2) = showTextParen (d > 1) $
    showText "\\text{let } " . showText v1 . showText " \\otimes " . showText v2 . showText " = " . showsLatexPrec 0 e1 .
    showText " \\text{ in } " . showsLatexPrec 0 e2
  showsLatexPrec _ Star = showText "*"
  showsLatexPrec d (Inl ty e1) = showTextParen (d > 10) $
    showText "\\text{inl} ^{" . textPrec 11 ty . showText "} \\space " . showsLatexPrec 11 e1
  showsLatexPrec d (Inr ty e1) = showTextParen (d > 10) $
    showText "\\text{inr} ^{" . textPrec 11 ty . showText "} \\space "  . showsLatexPrec 11 e1
  showsLatexPrec d (CasePlus e1 v1 e2 v2 e3) = showTextParen (d > 0) $
    showText "\\text{case } " . showsLatexPrec 3 e1 . showText " \\text{ of \
    \inl } " . showText v1 . showText " \\to " . showsLatexPrec 1 e2 . showText "\\text{; \
    \inr } " . showText v2 . showText " \\to " . showsLatexPrec 0 e3
  showsLatexPrec d (Absurd ty e1) = showTextParen (d > 10) $
    showText "\\text{absurd} ^{" . textPrec 11 ty . showText "} \\space " . showsLatexPrec 11 e1
  showsLatexPrec d (With e1 e2) = showTextParen (d > 4) $
    showsLatexPrec 5 e1 . showText " \\& " . showsLatexPrec 5 e2
  showsLatexPrec d (Fst e1) = showTextParen (d > 10) $
    showText "\\text{fst } " . showsLatexPrec 11 e1
  showsLatexPrec d (Snd e1) = showTextParen (d > 10) $
    showText "\\text{snd } " . showsLatexPrec 11 e1
  showsLatexPrec d (Fold ty body) = showTextParen (d > 10) $
    showText "\\text{fold} ^{" . textPrec 11 ty . showText "} \\space " . showsLatexPrec 11 body
  showsLatexPrec d (Unfold body) = showTextParen (d > 10) $
    showText "\\text{unfold } " . showsLatexPrec 11 body
  showsLatexPrec d (Fix v ty body) = showTextParen (d > 1) $
    showText "\\text{fix } (" . showText v . showText " : " . showsLatexPrec 0 ty . showText "). \\space  " . showsLatexPrec 0 body

type Serial = Integer

type Context = [(Var, Integer, Type)]

instance ShowText Context where
  text [] = "⋅"
  text [(v, _, t)] = v <> " : " <> text t
  text ((v, _, t) : ctx) = text ctx <> ", " <> v <> " : " <> text t

instance ShowLatex Context where
  showLatex = go []
    where
      underline v vs = if v `elem` vs
        then \x -> "\\underline{" <> x <> "}"
        else id
      go _ [] = "\\cdot"
      go vs [(v, _, t)] = underline v vs $ v <> " : " <> showLatex t
      go vs ((v, _, t) : ctx) = underline v vs $ go (v:vs) ctx <> ", " <> v <> " : " <> showLatex t

showLatexContextSimple :: Context -> Text
showLatexContextSimple [] = "\\cdot"
showLatexContextSimple [(v, _, _)] = v
showLatexContextSimple ((v, _, _) : ctx) = showLatexContextSimple ctx <> ", " <> v

data Decl
  = TypeDecl Name Type
  | TermDecl Name AST
  deriving Show

instance ShowText Decl where
  text (TypeDecl v ty) = "type " <> v <> " = " <> text ty
  text (TermDecl v e) = v <> " = " <> text e

type Source = [Decl]

instance ShowText Source where
  text decls = T.unlines (text <$> decls)

type Typing = (Var, Type)

instance ShowText Typing where
  text (name, ty) = name <> " : " <> text ty

instance ShowLatex Typing where
  showLatex (name, ty) = "\\text{" <> name <> "} : " <> showLatex ty

data Prototype
  = TypeProto Synonym
  | TermProto Typing

instance ShowText Prototype where
  text (TypeProto syn) = text syn
  text (TermProto typing) = text typing

type Interface = [Prototype]

instance ShowText Interface where
  text protos = T.unlines (text <$> protos)

instance {-# Overlapping #-} Show Interface where
  show = T.unpack . text

data Judgement
  = Judgement
    { inc  :: Context
    , out  :: Context
    , expr :: AST
    , ty   :: Type
    }

instance ShowText Judgement where
  text (Judgement inc out expr ty) = text inc <> " \\ " <> text out <> " |- " <> text expr <> " : " <> text ty

instance ShowLatex Judgement where
  showLatex (Judgement inc out expr ty) =
    showLatex inc <> " \\backslash " <> showLatexContextSimple out <> " \\vdash " <> showLatex expr <> " : " <> showLatex ty

data Frac
  = Frac [Frac] Judgement By
  | FracIntro Typing Judgement

instance ShowLatex Frac where
  showLatex (Frac l j by) = "\\displaystyle \\frac {" <> T.intercalate "\\qquad" (showLatex <$> l) <> "} {" <> showLatex j <> "} " <> showLatex by
  showLatex (FracIntro typing j) = "\\displaystyle \\frac {" <> showLatex typing <> "} {" <> showLatex j <> "} \\text{intro}"

data Latex
  = LatexFrac Frac
  | LatexSynonym Synonym

instance ShowLatex Latex where
  showLatex (LatexFrac frac) = showLatex frac
  showLatex (LatexSynonym syn) = showLatex syn

instance ShowText [Latex] where
  text = T.unlines . fmap ((<> " \\newline") . showLatex)
