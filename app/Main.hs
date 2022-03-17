module Main where

import AST
import Typecheck

exp1 :: AST
exp1 = Lam "f" (One :->: One) $ Lam "x" One $ Var "f" `App` Var "x"

exp2 :: AST
exp2 = Lam "f" (One :->: One :->: One) $ Lam "x" (One :*: One) $ LetTensor "a" "b" (Var "x") (Var "f" `App` Var "a" `App` Var "b")

exp3 :: AST
exp3 = Lam "x" (One :*: One) $ LetTensor "a" "b" (Var "x") $ Var "b"

exp4 :: AST
exp4 = Lam "y" One $ Lam "x" ((One :*: One) :+: One) $ CasePlus (Var "x") "a" (LetTensor "m" "n" (Var "a") (Var "m")) "b" (Var "y")

exp5 :: AST
exp5 = Lam "x" Zero $ Absurd One (Var "x")

exp6 :: AST
exp6 = Lam "b" (One :+: One) $ Lam "n" (One :&: One) $ CasePlus (Var "b") "x" (Fst (Var "n")) "y" (Snd (Var "n"))

nat :: Type
nat = TypeVar "Nat"

modal :: Type -> Type
modal = (TypeVar "!" :.:)

source :: Source
source =
  [ TypeDecl "Nat" $ Mu "a" $ One :+: TypeVar "a"
  , TypeDecl "!" $ TypeLam "A" Type $ Mu "a" $ TypeVar "A" :*: TypeVar "a"
  , TermDecl "zero" $ Fold nat $ Inl nat Star
  , TermDecl "succ" $ Lam "x" nat $ Fold nat $ Inr One (Var "x")
  , TermDecl "dup!" $ Lam "x" (modal nat) $ LetTensor "a" "x'" (Unfold (Var "x")) $ LetTensor "b" "x''" (Unfold (Var "x'")) $ Tensor (Var "a") (Var "b")
  , TermDecl "dup"  $ Fix "c" (modal $ nat :->: nat :*: nat) $ Lam "x" nat $ CasePlus (Unfold $ Var "x")
      "s" (Tensor (Var "zero") (Var "zero"))
      "p" $ LetTensor "rec" "d" (Unfold $ Var "c") $ LetTensor "x1" "x2" (Var "rec" `App` Var "p") $ Tensor (Var "succ" `App` Var "x1") (Var "succ" `App` Var "x2")
  , TermDecl "pred" $ Lam "x" nat $ CasePlus (Unfold (Var "x")) 
      "s" (Var "zero")
      "n" (Var "n")
  , TermDecl "zeros" $ Fix "p" (modal $ modal nat) $ LetTensor "q" "r" (Unfold $ Var "p") $ Fold (modal nat) $ Tensor (Var "zero") (Var "q")
  , TermDecl "plus" $ Fix "p" (modal $ nat :->: nat :->: nat) $ Lam "x" nat $ Lam "y" nat $ 
      CasePlus (Unfold (Var "x"))
        "s" (Var "y")
        "n" $ LetTensor "rec" "q" (Unfold (Var "p")) $ Var "succ" `App` (Var "rec" `App` Var "n" `App` Var "y")
  ]

main :: IO ()
main = runCheckSource source