{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module HVM where

import Prelude hiding (snd, fst)
import Data.Maybe
import qualified Data.Text as T
import Data.Text (Text)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.Text.IO as T

import Data
import Latex

type CtorName = Text
type VarName = Text

type HVMSrc = [HVM]

instance ShowText HVMSrc where
  text hvms = T.unlines $ map text hvms

data HVM = LHS := RHS

instance ShowText HVM where
  text (lhs := rhs) = text lhs <> " = " <> text rhs

data LHS = LHS CtorName [Pattern]

instance ShowText LHS where
  text (LHS ctorName []) = "(" <> ctorName <> ")"
  text (LHS ctorName patterns) = "(" <> ctorName <> " " <> T.unwords (text <$> patterns) <> ")"

data Pattern
  = CtorPat CtorName [Pattern]
  | VarPat VarName

instance ShowText Pattern where
  text (CtorPat ctorName []) = "(" <> ctorName <> ")"
  text (CtorPat ctorName patterns) = "(" <> ctorName <> " " <> T.unwords (text <$> patterns) <> ")"
  text (VarPat varName) = varName

data RHS
  = Apply Bool RHS [RHS]
  | Lambda VarName RHS
  | Intro Text

instance ShowText RHS where
  text (Apply _ f xs) = "(" <> T.unwords (text <$> f : xs) <> ")"
  text (Lambda v b) = "λ" <> v <> " " <> text b
  text (Intro v) = v

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

var :: Text -> RHS
var = Intro

fix :: VarName -> RHS -> RHS
fix p b = call "Fix" `apply` [Lambda p b]

translate :: AST -> RHS
translate (Lam s ast) = Lambda s (translate ast)
translate (App ast1 ast2) = translate ast1 `app` translate ast2
translate (Var s) = var s
translate (Call s) = call s
translate (Tensor ast1 ast2) = tensor (translate ast1) (translate ast2)
translate (LetTensor a b ast ast2) = letTensor a b (translate ast) (translate ast2)
translate Unit = unit
translate (Inl ast) = inl (translate ast)
translate (Inr ast) = inr (translate ast)
translate (CasePlus x w1 m1 w2 m2) = casePlus (translate x) w1 (translate m1) w2 (translate m2)
translate (Absurd ast) = absurd (translate ast)
translate (With ast1 ast2) = with (translate ast1) (translate ast2)
translate (Fst ast) = fst (translate ast)
translate (Snd ast) = snd (translate ast)
translate (Fold _ ast) = fold (translate ast)
translate (Unfold ast) = unfold (translate ast)
translate (Unfold' _ ast) = translate (Unfold ast)
translate (Fix p ast) = fix p (translate ast)

translateSrc :: Source -> HVMSrc
translateSrc = mapMaybe f
  where
    f (TypeDecl _ _) = Nothing
    f (DataDecl _ _) = Nothing
    f (TermDecl nm ast) = Just $ term nm := translate ast
    f (TermDeclTyped nm ast _) = Just $ term nm := translate ast

runtime :: ExpQ
runtime = do
  hvm <- runIO $ T.readFile "runtime.hvmp"
  lift hvm
