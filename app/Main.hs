module Main where

import ADT
import Typecheck

exp1 :: ADT
exp1 = Lam "f" (One :->: One) $ Lam "x" One $ Var "f" `App` Var "x"

exp2 :: ADT
exp2 = Lam "f" (One :->: One :->: One) $ Lam "x" (One :*: One) $ LetTensor "a" "b" (Var "x") (Var "f" `App` Var "a" `App` Var "b")

exp3 :: ADT
exp3 = Lam "x" (One :*: One) $ LetTensor "a" "b" (Var "x") $ Var "b"

exp4 :: ADT
exp4 = Lam "y" One $ Lam "x" ((One :*: One) :+: One) $ CasePlus (Var "x") "a" (LetTensor "m" "n" (Var "a") (Var "m")) "b" (Var "y")

exp5 :: ADT
exp5 = Lam "x" Zero $ Absurd One (Var "x")

exp6 :: ADT
exp6 = Lam "b" (One :+: One) $ Lam "n" (One :&: One) $ CasePlus (Var "b") "x" (Fst (Var "n")) "y" (Snd (Var "n"))

main :: IO ()
main = do
  putStrLn "\nexp1:\n"
  runCheck exp1
  putStrLn "\nexp2:\n"
  runCheck exp2
  putStrLn "\nexp3:\n"
  runCheck exp3
  putStrLn "\nexp4:\n"
  runCheck exp4
  putStrLn "\nexp5:\n"
  runCheck exp5
  putStrLn "\nexp6:\n"
  runCheck exp6
