{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Data where

import Data.Text (Text)
import qualified Data.Text as T

import Latex

default (Text)

type Var = Text
type Name = Text

---------- Kind ----------

data Kind
  = Type
  | Kind :->> Kind
  deriving (Eq, Show)

instance ShowText Kind where
  textPrec _ Type = showText "*"
  textPrec d (a :->> b) = showTextParen (d > 5) $ textPrec 6 a . showText " -> " . textPrec 5 b

instance ShowLatex Kind where
  showsLatexPrec _ Type = showText "*"
  showsLatexPrec d (a :->> b) = showTextParen (d > 5) $ showsLatexPrec 6 a . showText " \\to " . showsLatexPrec 5 b

---------- Type ----------

data TConst = TOne | TZero deriving (Show, Eq)

data TOp = TArr | TTensor | TPlus | TWith
  deriving (Show, Eq)

data Type
  = TConst TConst
  | TOp TOp Type Type
  | TVar Var
  | TCall Name
  | TMu Var Type
  | TLam Var Kind Type
  | TApp Type Type
  deriving (Show, Eq)

pattern One :: Type
pattern One = TConst TOne

pattern Zero :: Type
pattern Zero = TConst TZero

pattern (:->) :: Type -> Type -> Type
pattern (:->) a b = TOp TArr a b
infixr 5 :->

pattern (:*:) :: Type -> Type -> Type
pattern (:*:) a b = TOp TArr a b
infixl 7 :*:

pattern (:+:) :: Type -> Type -> Type
pattern (:+:) a b = TOp TPlus a b
infixr 6 :+:

pattern (:&:) :: Type -> Type -> Type
pattern (:&:) a b = TOp TWith a b
infixl 7 :&:

instance ShowText Type where
  textPrec _ One = showText "1"
  textPrec _ Zero = showText "0"
  textPrec _ (TVar v) = showText v
  textPrec _ (TCall n) = showText n
  textPrec d (t1 :-> t2) = showTextParen (d > 5) $ textPrec 6 t1 . showText " ⊸ " . textPrec 5 t2
  textPrec d (t1 :*: t2)  = showTextParen (d > 7) $ textPrec 8 t1 . showText " ⊗ " . textPrec 8 t2
  textPrec d (t1 :+: t2)  = showTextParen (d > 6) $ textPrec 7 t1 . showText " ⊕ " . textPrec 7 t2
  textPrec d (t1 :&: t2)  = showTextParen (d > 7) $ textPrec 8 t1 . showText " & " . textPrec 8 t2
  textPrec d (TMu v t) = showTextParen (d > 1) $ showText "μ " . showText v . showText ". " . textPrec 1 t
  textPrec d (TLam v k t2) = showTextParen (d > 1) $ showText "λ (" . showText v . showText " : " . textPrec 0 k . showText "). " . textPrec 0 t2
  textPrec d (t1 `TApp` t2) = showTextParen (d > 10) $ textPrec 10 t1 . showText " " . textPrec 11 t2

instance ShowLatex Type where
  showsLatexPrec _ One = showText "\\bold{1}"
  showsLatexPrec _ Zero = showText "\\bold{0}"
  showsLatexPrec _ (TVar v) = showText v
  showsLatexPrec _ (TCall n) = showText n
  showsLatexPrec d (t1 :-> t2) = showTextParen (d > 5) $ showsLatexPrec 6 t1 . showText " \\multimap " . showsLatexPrec 5 t2
  showsLatexPrec d (t1 :*: t2) = showTextParen (d > 7) $ showsLatexPrec 8 t1 . showText " \\otimes " . showsLatexPrec 8 t2
  showsLatexPrec d (t1 :+: t2) = showTextParen (d > 6) $ showsLatexPrec 7 t1 . showText " \\oplus " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :&: t2) = showTextParen (d > 7) $ showsLatexPrec 8 t1 . showText " \\& " . showsLatexPrec 8 t2
  showsLatexPrec d (TMu v t) = showTextParen (d > 1) $ showText "\\mu " . showText v . showText " . \\space " . showsLatexPrec 1 t
  showsLatexPrec d (TLam v k t2) = showTextParen (d > 1) $ showText "\\lambda (" . showText v . showText  " : " . showsLatexPrec 0 k . showText "). \\space " . showsLatexPrec 1 t2
  showsLatexPrec d (t1 `TApp` t2) = showTextParen (d > 10) $ showsLatexPrec 10 t1 . showText " \\space " . showsLatexPrec 11 t2

typesize :: Type -> Int
typesize (TConst _) = 1
typesize (TVar _) = 1
typesize (TCall _) = 1
typesize (TOp _ t1 t2) = 1 + typesize t1 + typesize t2
typesize (TMu _ t) = 1 + typesize t
typesize (TLam _ _ t) = 1 + typesize t
typesize (t1 `TApp` t2) = 1 + typesize t1 + typesize t2

instance Ord Type where
  a `compare` b = typesize a `compare` typesize b

---------- Synonym ----------

data SynDef
  = Syn Type Kind
  | Data Kind
  deriving (Show)

type Synonym = (Name, SynDef)

instance ShowText Synonym where
  text (nm, Syn ty k) = "type " <> nm <> " = " <> text ty <> " : " <> text k
  text (nm, Data k) = "data " <> nm <> " : " <> text k

instance ShowLatex Synonym where
  showLatex (nm, Syn ty k) = "\\text{type } " <> nm <> " = " <> showLatex ty <> " : " <> showLatex k
  showLatex (nm, Data k) = "\\text{data } " <> nm <> " : " <> showLatex k

---------- Context ----------

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

---------- AST ----------

data AST
  = Lam Var AST                   -- λ Var. AST
  | App AST AST                   -- AST AST
  | Var Var                       -- Var
  | Call Name                     -- Name
  | Tensor AST AST                -- AST * AST
  | LetTensor Var Var AST AST     -- let Var * Var = AST in AST
  | Inl AST                       -- inl AST
  | Inr AST                       -- inr AST
  | CasePlus AST Var AST Var AST  -- case AST of inl Var -> AST | inr Var -> AST
  | With AST AST                  -- AST & AST
  | Fst AST                       -- fst AST
  | Snd AST                       -- snd AST
  | Unit                          -- tt
  | Absurd AST                    -- absurd AST
  | Fold Type AST
  | Unfold AST
  | Unfold' Type AST
  | Fix Var AST
  deriving Show

instance ShowText AST where
  textPrec d (Lam v e) = showTextParen (d > 1) $
    showText "λ " . showText v . showText ". " . textPrec 0 e
  textPrec d (App e1 e2) = showTextParen (d > 10) $
    textPrec 10 e1 . showText " " . textPrec 11 e2
  textPrec _ (Var v) = showText v
  textPrec _ (Call c) = showText c
  textPrec d (Tensor e1 e2) = showTextParen (d > 4) $
    textPrec 5 e1 . showText " ⊗ " . textPrec 5 e2
  textPrec d (LetTensor v1 v2 e1 e2) = showTextParen (d > 1) $
    showText "let " . showText v1 . showText " ⊗ " . showText v2 . showText " = " . textPrec 0 e1 . showText " in " . textPrec 0 e2
  textPrec _ Unit = showText "tt"
  textPrec d (Inl e1) = showTextParen (d > 10) $
    showText "inl " . textPrec 11 e1
  textPrec d (Inr e1) = showTextParen (d > 10) $
    showText "inr " . textPrec 11 e1
  textPrec d (CasePlus e1 v1 e2 v2 e3) = showTextParen (d > 0) $
    showText "case " . textPrec 3 e1 . showText " of \
    \inl " . showText v1 . showText " -> " . textPrec 1 e2 . showText " | \
    \inr " . showText v2 . showText " -> " . textPrec 1 e3
  textPrec d (Absurd e1) = showTextParen (d > 10) $
    showText "absurd " . textPrec 11 e1
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
  textPrec d (Unfold' ty body) = showTextParen (d > 10) $
    showText "unfold' " . textPrec 11 ty . showText " " . textPrec 11 body
  textPrec d (Fix v body) = showTextParen (d > 1) $
    showText "fix " . showText v . showText ". " . textPrec 0 body

instance ShowLatex AST where
  showsLatexPrec d (Lam v e) = showTextParen (d > 1) $
    showText "\\lambda " . showText v . showText ". \\space " . showsLatexPrec 0 e
  showsLatexPrec d (App e1 e2) = showTextParen (d > 10) $
    showsLatexPrec 10 e1 . showText " \\space " . showsLatexPrec 11 e2
  showsLatexPrec _ (Var v) = showText v
  showsLatexPrec _ (Call c) = showText "\\text{" . showText c . showText "}"
  showsLatexPrec d (Tensor e1 e2) = showTextParen (d > 4) $
    showsLatexPrec 5 e1 . showText " \\otimes " . showsLatexPrec 5 e2
  showsLatexPrec d (LetTensor v1 v2 e1 e2) = showTextParen (d > 1) $
    showText "\\text{let } " . showText v1 . showText " \\otimes " . showText v2 . showText " = " . showsLatexPrec 0 e1 .
    showText " \\text{ in } " . showsLatexPrec 0 e2
  showsLatexPrec _ Unit = showText "\\text{tt}"
  showsLatexPrec d (Inl e1) = showTextParen (d > 10) $
    showText "\\text{inl } " . showsLatexPrec 11 e1
  showsLatexPrec d (Inr e1) = showTextParen (d > 10) $
    showText "\\text{inr }" . showsLatexPrec 11 e1
  showsLatexPrec d (CasePlus e1 v1 e2 v2 e3) = showTextParen (d > 0) $
    showText "\\text{case } " . showsLatexPrec 3 e1 . showText " \\text{ of \
    \inl } " . showText v1 . showText " \\to " . showsLatexPrec 1 e2 . showText "\\text{ | \
    \inr } " . showText v2 . showText " \\to " . showsLatexPrec 0 e3
  showsLatexPrec d (Absurd e1) = showTextParen (d > 10) $
    showText "\\text{absurd }" . showsLatexPrec 11 e1
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
  showsLatexPrec d (Unfold' ty body) = showTextParen (d > 10) $
    showText "\\text{unfold } ^{" . textPrec 11 ty . showText "} \\space " . showsLatexPrec 11 body
  showsLatexPrec d (Fix v body) = showTextParen (d > 1) $
    showText "\\text{fix }" . showText v . showText ". \\space  " . showsLatexPrec 0 body

---------- Judgement ----------

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

---------- Frac ----------

data Frac
  = Frac [Frac] Judgement By
  | FracIntro Typing Judgement

instance ShowLatex Frac where
  showLatex (Frac l j by) = "\\displaystyle \\frac {" <> T.intercalate "\\qquad" (showLatex <$> l) <> "} {" <> showLatex j <> "} " <> showLatex by
  showLatex (FracIntro typing j) = "\\displaystyle \\frac {" <> showLatex typing <> "} {" <> showLatex j <> "} \\text{intro}"

---------- Latex ----------

data Latex
  = LatexFrac Name Frac
  | LatexSynonym Synonym

instance ShowLatex Latex where
  showLatex (LatexFrac name frac) = "\\text{" <> name <> "} : " <> showLatex frac
  showLatex (LatexSynonym syn) = showLatex syn

instance ShowText [Latex] where
  text = T.unlines . fmap ((<> " \\newline") . showLatex)

---------- Typing ----------

type Typing = (Name, Type)

instance ShowText Typing where
  text (name, ty) = name <> " : " <> text ty

instance ShowLatex Typing where
  showLatex (name, ty) = "\\text{" <> name <> "} : " <> showLatex ty

---------- Prototype ----------

data Prototype
  = SynProto Synonym
  | TermProto Typing

instance ShowText Prototype where
  text (SynProto syn) = text syn
  text (TermProto typing) = text typing

---------- Interface ----------

type Interface = [Prototype]

instance ShowText Interface where
  text protos = T.unlines (text <$> protos)

instance {-# Overlapping #-} Show Interface where
  show = T.unpack . text

---------- Decl ----------

data Decl
  = TypeDecl Name Type
  | DataDecl Name Kind
  | TermDecl Name AST
  | TermDeclTyped Name AST Type
  deriving Show

instance ShowText Decl where
  text (TypeDecl v ty) = "type " <> v <> " = " <> text ty
  text (DataDecl v k) = "data " <> v <> " : " <> text k
  text (TermDecl v e) = v <> " = " <> text e
  text (TermDeclTyped v e ty) = v <> " = " <> text e <> " : " <> text ty

---------- Source ----------

type Source = [Decl]

instance ShowText Source where
  text decls = T.unlines (text <$> decls)
