module HVM where

import Data.String
import Prelude hiding (snd, fst)
import Data.Maybe

import AST

type CtorName = String
type VarName = String

newtype HVMSrc = HVMSrc [HVM]

instance Show HVMSrc where
  show (HVMSrc hvms) = unlines $ map show hvms

data HVM = LHS := RHS

instance Show HVM where
  show (lhs := rhs) = show lhs <> " = " <> show rhs

data LHS = LHS CtorName [Pattern]

instance Show LHS where
  show (LHS ctorName []) = "(" <> ctorName <> ")"
  show (LHS ctorName patterns) = "(" <> ctorName <> " " <> unwords (show <$> patterns) <> ")"

data Pattern
  = CtorPat CtorName [Pattern]
  | VarPat VarName

instance Show Pattern where
  show (CtorPat ctorName []) = "(" <> ctorName <> ")"
  show (CtorPat ctorName patterns) = "(" <> ctorName <> " " <> unwords (show <$> patterns) <> ")"
  show (VarPat varName) = varName

data RHS
  = Apply Bool RHS [RHS]
  | Lambda VarName RHS
  | Intro String

instance Show RHS where
  show (Apply _ f xs) = "(" <> unwords (show <$> f : xs) <> ")"
  show (Lambda v b) = "λ" <> v <> " " <> show b
  show (Intro v) = v

term :: CtorName -> LHS
term s = LHS s []

apply :: RHS -> [RHS] -> RHS
apply = Apply False

app :: RHS -> RHS -> RHS
(Apply True f xs) `app` x = Apply True f (xs <> [x])
a `app` b = Apply True a [b]

tensor :: RHS -> RHS -> RHS
tensor a b = Intro "Tensor" `app` a `app` b

letTensor :: VarName -> VarName -> RHS -> RHS -> RHS
letTensor a b x p = Intro "LetTensor" `apply` [x] `app` Lambda a (Lambda b p)

unit :: RHS
unit = Intro "Unit"

inl :: RHS -> RHS
inl = (Intro "Inl" `app`)

inr :: RHS -> RHS
inr = (Intro "Inr" `app`)

casePlus :: RHS -> VarName -> RHS -> VarName -> RHS -> RHS
casePlus x vl l vr r = Intro "CasePlus" `apply` [x] `app` Lambda vl l `app` Lambda vr r

absurd :: RHS -> RHS
absurd a = Intro "Absurd" `app` a

with :: RHS -> RHS -> RHS
with a b = Intro "With" `apply` [a, b]

fst :: RHS -> RHS
fst a = Intro "Fst" `apply` [a]

snd :: RHS -> RHS
snd a = Intro "Snd" `apply` [a]

fold :: RHS -> RHS
fold x = x

unfold :: RHS -> RHS
unfold x = x

call :: CtorName -> RHS
call f = Intro f `apply` []

var :: String -> RHS
var = Intro

fix :: VarName -> RHS -> RHS
fix p b = call "Fix" `apply` [Lambda p b]

translate :: AST -> RHS
translate (Lam s _ ast) = Lambda s (translate ast)
translate (App ast1 ast2) = translate ast1 `app` translate ast2
translate (Var s) = var s
translate (Call s) = call s
translate (Tensor ast1 ast2) = tensor (translate ast1) (translate ast2)
translate (LetTensor a b ast ast2) = letTensor a b (translate ast) (translate ast2)
translate Star = unit
translate (Inl _ ast) = inl (translate ast)
translate (Inr _ ast) = inr (translate ast)
translate (CasePlus x w1 m1 w2 m2) = casePlus (translate x) w1 (translate m1) w2 (translate m2)
translate (Absurd _ ast) = absurd (translate ast)
translate (With ast1 ast2) = with (translate ast1) (translate ast2)
translate (Fst ast) = fst (translate ast)
translate (Snd ast) = snd (translate ast)
translate (Fold _ ast) = fold (translate ast)
translate (Unfold ast) = unfold (translate ast)
translate (Fix p _ ast) = fix p (translate ast)

traslateSrc :: Source -> HVMSrc
traslateSrc = HVMSrc . mapMaybe f
  where
    f (TypeDecl _ _) = Nothing
    f (TermDecl nm ast) = Just $ term nm := translate ast
