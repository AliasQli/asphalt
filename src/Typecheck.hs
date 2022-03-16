module Typecheck where

import Control.Monad.Except
import Control.Monad.RWS
import ADT
import Latex
import Data.Bifunctor
import Data.List (intersect)

type Typecheck = ExceptT String (RWS () String (Context, Int))

serial :: Typecheck Int
serial = do
  (context, i) <- get
  put (context, i + 1)
  pure i

modContext :: (Context -> Context) -> Typecheck ()
modContext = modify . first

getContext :: Typecheck Context
getContext = fst <$> get

putContext :: Context -> Typecheck ()
putContext = modContext . const

strip :: Int -> Context -> Context
strip i = filter (\(_, b, _) -> b /= i)

lookupVar :: Var -> Typecheck (Int, Type)
lookupVar v = do
  context <- getContext
  case filter (\(a, _, _) -> a == v) context of
    (_, i, t) : _ -> pure (i, t)
    [] -> throwError $ "Unbound variable: " ++ v

tellJudgement :: Judgement -> Typecheck ()
tellJudgement = tell . (++ "\n") . show

retLatex :: Latex -> Typecheck (Type, Latex)
retLatex latex@(Latex _ j _) = do
  tellJudgement j
  pure (ty j, latex)

typecheck :: ADT -> Typecheck (Type, Latex)
typecheck adt@(Lam var ty body) = do
  i <- serial
  inc <- getContext
  modContext ((var, i, ty) :)
  (ty', premise) <- typecheck body
  modContext (strip i)
  out <- getContext
  retLatex $ Latex [premise] (Judgement inc out adt (ty :->: ty')) LolipopI
typecheck adt@(App f x) = do
  inc <- getContext
  (fTy, fPremise) <- typecheck f
  (xTy, xPremise) <- typecheck x
  out <- getContext
  case fTy of
    ty :->: ty' -> do
      unless (ty == xTy) $ throwError $ "type mismatch: can't apply " <> show f <> " : " <> show fTy <> " to " <> show x <> " : " <> show xTy
      retLatex $ Latex [fPremise, xPremise] (Judgement inc out adt ty') LolipopE
    _ -> throwError $ "type mismatch: " <> show f <> " : " <> show fTy <> " is not a function type"
typecheck adt@(Var var) = do
  inc <- getContext
  (i, ty) <- lookupVar var
  modContext (strip i)
  out <- getContext
  retLatex $ Latex [] (Judgement inc out adt ty) Nil
typecheck adt@(Tensor a b) = do
  inc <- getContext
  (aTy, aPremise) <- typecheck a
  (bTy, bPremise) <- typecheck b
  out <- getContext
  retLatex $ Latex [aPremise, bPremise] (Judgement inc out adt (aTy :*: bTy)) TensorI
typecheck adt@(LetTensor v1 v2 t body) = do
  inc <- getContext
  (tTy, tPremise) <- typecheck t
  case tTy of
    aTy :*: bTy -> do
      ai <- serial
      bi <- serial
      modContext (((v2, bi, bTy) :) . ((v1, ai, aTy) :))
      (ty, premise) <- typecheck body
      modContext (strip ai . strip bi)
      out <- getContext
      retLatex $ Latex [tPremise, premise] (Judgement inc out adt ty) TensorE
    _ -> throwError $ "type mismatch: " <> show t <> " : " <> show tTy <> " is not a tensor type"
typecheck adt@Star = do
  inc <- getContext
  let out = inc
  retLatex $ Latex [] (Judgement inc out adt One) OneI
typecheck adt@(Inl bTy a) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  out <- getContext
  retLatex $ Latex [premise] (Judgement inc out adt (aTy :+: bTy)) TensorI
typecheck adt@(Inr aTy b) = do
  inc <- getContext
  (bTy, premise) <- typecheck b
  out <- getContext
  retLatex $ Latex [premise] (Judgement inc out adt (aTy :+: bTy)) TensorI
typecheck adt@(CasePlus x v1 b1 v2 b2) = do
  inc <- getContext
  (xTy, premise) <- typecheck x
  case xTy of
    aTy :+: bTy -> do
      backup <- getContext
      i1 <- serial
      modContext ((v1, i1, aTy) :)
      (b1Ty, b1Premise) <- typecheck b1
      modContext (strip i1)
      context1 <- getContext
      putContext backup
      i2 <- serial
      modContext ((v2, i2, bTy) :)
      (b2Ty, b2Premise) <- typecheck b2
      modContext (strip i2)
      context2 <- getContext
      let out = context1 `intersect` context2
      if b1Ty == b2Ty
        then retLatex $ Latex [premise, b1Premise, b2Premise] (Judgement inc out adt b1Ty) PlusE
        else throwError $ "type mismatch: " <> show b1 <> " : " <> show b1Ty <> " and " <> show b2 <> " : " <> show b2Ty <> " are not the same type"
    _ -> throwError $ "type mismatch: " <> show x <> " : " <> show xTy <> " is not a sum type"
typecheck adt@(Absurd ty a) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  case aTy of
    Zero -> do
      out <- getContext
      retLatex $ Latex [premise] (Judgement inc out adt ty) ZeroE
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not 0"
typecheck adt@(With a b) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  context1 <- getContext
  putContext inc
  (bTy, premise') <- typecheck b
  context2 <- getContext
  let out = context1 `intersect` context2
  retLatex $ Latex [premise, premise'] (Judgement inc out adt (aTy :&: bTy)) WithI
typecheck adt@(Fst a) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  case aTy of
    ty :&: _ -> do
      out <- getContext
      retLatex $ Latex [premise] (Judgement inc out adt ty) WithEL
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not a with type"
typecheck adt@(Snd a) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  case aTy of
    _ :&: ty -> do
      out <- getContext
      retLatex $ Latex [premise] (Judgement inc out adt ty) WithER
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not a with type"

runCheck :: ADT -> IO ()
runCheck e = do
  let (eth, log) = evalRWS (runExceptT (typecheck e)) () ([], 0)
  putStrLn log
  case eth of
    Left err -> putStrLn ("Error: " ++ err)
    Right (t, latex) -> do
      putStrLn $ show e <> " : " <> show t <> "\n"
      print latex
