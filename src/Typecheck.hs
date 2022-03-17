{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Typecheck where

import Control.Monad.Except
import Control.Monad.RWS hiding (gets)
import AST
import Latex
import Data.List (intersect)
import GHC.Records
import Data.Functor.Const
import Control.Monad.Identity
import Data.Maybe

type Lens s a = forall f. Functor f => (a -> f a) -> s -> f s

lens :: (s -> a) -> (s -> a -> s) -> Lens s a
lens getter setter f s = setter s <$> f (getter s)

_1 :: Lens (a, b, c, d) a
_1 f (a, b, c, d) = fmap (, b, c, d) (f a)

_2 :: Lens (a, b, c, d) b
_2 f (a, b, c, d) = fmap (a, , c, d) (f b)

_3 :: Lens (a, b, c, d) c
_3 f (a, b, c, d) = fmap (a, b, , d) (f c)

_4 :: Lens (a, b, c, d) d
_4 f (a, b, c, d) = fmap (a, b, c, ) (f d)

view :: Lens s a -> s -> a
view l s = getConst $ l Const s

over :: Lens s a -> (a -> a) -> s -> s
over l f s = runIdentity $ l (Identity . f) s

gets :: MonadState s m => Lens s a -> m a
gets l = view l <$> get

modifies :: MonadState s m => Lens s a -> (a -> a) -> m ()
modifies l f = modify (over l f)

puts :: MonadState s m => Lens s a -> a -> m ()
puts l a = modifies l (const a)

type Typecheck = ExceptT String (RWS () String (Synonyms, [Typing], Context, Int))

serial :: Typecheck Int
serial = do
  i <- gets _4
  puts _4 (i + 1)
  pure i

modContext :: (Context -> Context) -> Typecheck ()
modContext = modifies _3

getContext :: Typecheck Context
getContext = gets _3

putContext :: Context -> Typecheck ()
putContext = puts _3

getTypings :: Typecheck [Typing]
getTypings = gets _2

modTypings :: ([Typing] -> [Typing]) -> Typecheck ()
modTypings = modifies _2

getSynonyms :: Typecheck Synonyms
getSynonyms = gets _1

modSynonyms :: (Synonyms -> Synonyms) -> Typecheck ()
modSynonyms = modifies _1

strip :: Int -> Context -> Context
strip i = filter (\(_, b, _) -> b /= i)

tellJudgement :: Judgement -> Typecheck ()
tellJudgement = tell . (++ "\n") . show

retLatex :: Latex -> Typecheck (Type, Latex)
retLatex latex@(Latex _ j _) = do
  tellJudgement j
  pure (getField @"ty" j, latex)

normalizeType :: Type -> Typecheck Type
normalizeType ty = do
  synonyms <- getSynonyms
  case normalize synonyms [] ty of
    Just (ty, Type) -> pure ty
    Just (ty, _) -> throwError $ "type mismatch: " <> show ty <> " is not of kind *"
    Nothing -> throwError $ "type mismatch: " <> show ty <> " is not closed"

checkWellType :: Type -> Typecheck ()
checkWellType = void . normalizeType

whnfType' :: [(Var, Kind)] -> Type -> Typecheck Type
whnfType' vs ty = do
  synonyms <- getSynonyms
  case whnf synonyms vs ty of
    Just ty -> pure ty
    Nothing -> throwError $ "type mismatch: " <> show ty <> " is not closed"

whnfType :: Type -> Typecheck Type
whnfType = whnfType' []

maybeModalType :: Type -> Typecheck (Maybe Type)
maybeModalType ty = do
  tyW <- whnfType ty
  case tyW of
    Mu v ty -> do
      tyW <- whnfType' [(v, Type)] ty
      case tyW of
        ty :*: TypeVar s
          | v == s -> pure $ Just ty
        _ -> pure Nothing
    _ -> pure Nothing

typecheck :: AST -> Typecheck (Type, Latex)
typecheck adt@(Lam var ty body) = do
  checkWellType ty
  i <- serial
  inc <- getContext
  modContext ((var, i, ty) :)
  (ty', premise) <- typecheck body
  modContext (strip i)
  out <- getContext
  retLatex $ latex [premise] (Judgement inc out adt (ty :->: ty')) LolipopI
typecheck adt@(App f x) = do
  inc <- getContext
  (fTy, fPremise) <- typecheck f
  (xTy, xPremise) <- typecheck x
  out <- getContext
  fTyW <- whnfType fTy
  case fTyW of
    ty :->: ty' -> do
      tyN <- normalizeType ty
      xTyN <- normalizeType xTy
      unless (tyN == xTyN) $ throwError $ "type mismatch: can't apply " <> show f <> " : " <> show fTy <> " to " <> show x <> " : " <> show xTy
      retLatex $ latex [fPremise, xPremise] (Judgement inc out adt ty') LolipopE
    _ -> throwError $ "type mismatch: " <> show f <> " : " <> show fTy <> " is not of a function type"
typecheck adt@(Var var) = do
  inc <- getContext
  case filter (\(a, _, _) -> a == var) inc of
    (_, i, ty) : _ -> do
      modContext (strip i)
      out <- getContext
      retLatex $ latex [] (Judgement inc out adt ty) Nil
    [] -> do
      global <- getTypings
      case filter (\(Typing a _) -> a == var) global of
        typing@(Typing _ ty) : _ -> do
          let out = inc
          retLatex $ Latex (Right typing) (Judgement inc out adt ty) Intro
        [] -> throwError $ "variable not found in context or global terms: " ++ var
typecheck adt@(Tensor a b) = do
  inc <- getContext
  (aTy, aPremise) <- typecheck a
  (bTy, bPremise) <- typecheck b
  out <- getContext
  retLatex $ latex [aPremise, bPremise] (Judgement inc out adt (aTy :*: bTy)) TensorI
typecheck adt@(LetTensor v1 v2 t body) = do
  inc <- getContext
  (tTy, tPremise) <- typecheck t
  tTyW <- whnfType tTy
  case tTyW of
    aTy :*: bTy -> do
      ai <- serial
      bi <- serial
      modContext (((v2, bi, bTy) :) . ((v1, ai, aTy) :))
      (ty, premise) <- typecheck body
      modContext (strip ai . strip bi)
      out <- getContext
      retLatex $ latex [tPremise, premise] (Judgement inc out adt ty) TensorE
    _ -> throwError $ "type mismatch: " <> show t <> " : " <> show tTy <> " is not of a tensor type"
typecheck adt@Star = do
  inc <- getContext
  let out = inc
  retLatex $ latex [] (Judgement inc out adt One) OneI
typecheck adt@(Inl bTy a) = do
  checkWellType bTy
  inc <- getContext
  (aTy, premise) <- typecheck a
  out <- getContext
  retLatex $ latex [premise] (Judgement inc out adt (aTy :+: bTy)) TensorI
typecheck adt@(Inr aTy b) = do
  checkWellType aTy
  inc <- getContext
  (bTy, premise) <- typecheck b
  out <- getContext
  retLatex $ latex [premise] (Judgement inc out adt (aTy :+: bTy)) TensorI
typecheck adt@(CasePlus x v1 b1 v2 b2) = do
  inc <- getContext
  (xTy, premise) <- typecheck x
  xTyW <- whnfType xTy
  case xTyW of
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
      b1TyN <- normalizeType b1Ty
      b2TyN <- normalizeType b2Ty
      if b1TyN == b2TyN
        then retLatex $ latex [premise, b1Premise, b2Premise] (Judgement inc out adt (min b1Ty b2Ty)) PlusE
        else throwError $ "type mismatch: " <> show b1 <> " : " <> show b1Ty <> " and " <> show b2 <> " : " <> show b2Ty <> " are not of the same type"
    _ -> throwError $ "type mismatch: " <> show x <> " : " <> show xTy <> " is not of a sum type"
typecheck adt@(Absurd ty a) = do
  checkWellType ty
  inc <- getContext
  (aTy, premise) <- typecheck a
  aTyW <- whnfType aTy
  case aTyW of
    Zero -> do
      out <- getContext
      retLatex $ latex [premise] (Judgement inc out adt ty) ZeroE
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not of type 0"
typecheck adt@(With a b) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  context1 <- getContext
  putContext inc
  (bTy, premise') <- typecheck b
  context2 <- getContext
  let out = context1 `intersect` context2
  retLatex $ latex [premise, premise'] (Judgement inc out adt (aTy :&: bTy)) WithI
typecheck adt@(Fst a) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  aTyW <- whnfType aTy
  case aTyW of
    ty :&: _ -> do
      out <- getContext
      retLatex $ latex [premise] (Judgement inc out adt ty) WithEL
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not of a with type"
typecheck adt@(Snd a) = do
  inc <- getContext
  (aTy, premise) <- typecheck a
  aTyW <- whnfType aTy
  case aTyW of
    _ :&: ty -> do
      out <- getContext
      retLatex $ latex [premise] (Judgement inc out adt ty) WithER
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not of a with type"
typecheck adt@(Fold ty body) = do
  checkWellType ty
  tyW <- whnfType ty
  case tyW of
    Mu v t -> do
      let expanded = expand (Just ty) v t
      inc <- getContext
      (ty', premise) <- typecheck body
      out <- getContext
      expandedN <- normalizeType expanded
      tyN' <- normalizeType ty'
      if expandedN == tyN'
        then retLatex $ latex [premise] (Judgement inc out adt ty) MuI
        else throwError $ "type mismatch: " <> show body <> " : " <> show ty' <> " is not of type " <> show expanded
    _ -> throwError $ "type mismatch: " <> show ty <> " is not a recursive type"
typecheck adt@(Unfold body) = do
  inc <- getContext
  (ty, premise) <- typecheck body
  out <- getContext
  tyW <- whnfType ty
  case tyW of
    Mu v t -> do
      let expanded = expand (Just ty) v t
      tell $ show (ty, tyW, expanded)
      retLatex $ latex [premise] (Judgement inc out adt expanded) MuE
    _ -> throwError $ "type mismatch: " <> show ty <> " is not a recursive type"
typecheck adt@(Fix v ty body) = do
  maybeTy <- maybeModalType ty
  case maybeTy of
    Just innerTyW -> do
      inc <- getContext
      incN <- sequence $ maybeModalType <$> ((\(_, _, c) -> c) <$> inc)
      if all isJust incN
        then do
          i <- serial
          modContext ((v, i, ty) :)
          (ty', premise) <- typecheck body
          innerTyN <- normalizeType innerTyW
          tyN' <- normalizeType ty'
          if innerTyN == tyN'
            then retLatex $ latex [premise] (Judgement inc [] adt (min innerTyW ty')) ByFix
            else throwError $ "type mismatch: " <> show body <> " : " <> show ty' <> " is not of type " <> show innerTyW
        else throwError $ "type mismatch: current context `" <> show inc <> "` contains non-modal type"
    Nothing -> throwError $ "type mismatch: " <> show ty <> " is not a modal type"

typecheckSource :: Source -> Typecheck [Either Synonym (Typing, Latex)]
typecheckSource [] = pure []
typecheckSource (TypeDecl v ty : decls) = do
  tell "\n"
  synonyms <- getSynonyms
  let maybeN = normalize synonyms [] ty
  case maybeN of
    Just (tyN, k) -> do
      modSynonyms ((v, (ty, tyN, k)) :)
      tell $ "type " <> v <> " = " <> show tyN <> " : " <> show k <> "\n"
      ress <- typecheckSource decls
      pure $ Left (Synonym v tyN k) : ress
    Nothing -> throwError $ "type mismatch: " <> show ty <> " is not closed"
typecheckSource (TermDecl v ast : rest) = do
  tell $ v <> ": \n"
  res <- typecheck ast
  tell "\n"
  let typing = Typing v (fst res)
  modTypings (typing :)
  ress <- typecheckSource rest
  pure $ Right (typing, snd res) : ress

runCheck :: AST -> IO ()
runCheck e = do
  let (eth, log) = evalRWS (runExceptT (typecheck e)) () ([], [], [], 0)
  putStrLn log
  case eth of
    Left err -> putStrLn ("Error: " ++ err)
    Right (t, latex) -> do
      putStrLn $ show e <> " : " <> show t <> "\n"
      putStrLn (showLatex latex)

runCheckSource :: Source -> IO ()
runCheckSource src = do
  let (eth, log) = evalRWS (runExceptT (typecheckSource src)) () ([], [], [], 0)
  putStrLn log
  case eth of
    Left err -> putStrLn ("Error: " ++ err)
    Right ress -> do
      putStrLn "Code:\n"
      print src
      putStrLn "Typechecking results:\n"
      forM_ ress $ \case
        Left syn -> do
          print syn
        Right (typing, _) -> do
          print typing
      putStrLn "\nLatex:\n"
      forM_ ress $ \case
        Left syn -> do
          putStrLn $ showLatex syn <> " \\newline"
        Right (Typing v _, latex) -> do
          putStrLn $ "\\text{" <> v <> "} : " <> showLatex latex <> " \\newline"
