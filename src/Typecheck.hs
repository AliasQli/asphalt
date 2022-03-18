{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Typecheck where

import Control.Monad.Except
import Control.Monad.State hiding (gets)
import Control.Monad.Writer
import Data.List (intersect)
import Data.Functor.Const
import Control.Monad.Identity

import AST
import Latex
import HVM

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

type Typecheck = ExceptT String (WriterT String (WriterT [Latex] (State ([Synonym], [Typing], Context, Serial))))

serial :: Typecheck Serial
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

addToCtx :: Var -> Type -> Typecheck Serial
addToCtx var ty = do
  i <- serial
  modContext ((var, i, ty) :)
  pure i

removeFromCtx :: Serial -> Typecheck ()
removeFromCtx i = modContext (strip i)
  where
    strip :: Serial -> Context -> Context
    strip i = filter (\(_, b, _) -> b /= i)

withAddition :: Var -> Type -> Typecheck a -> Typecheck a
withAddition var ty action = do
  i <- addToCtx var ty
  a <- action
  removeFromCtx i
  pure a

getTypings :: Typecheck [Typing]
getTypings = gets _2

modTypings :: ([Typing] -> [Typing]) -> Typecheck ()
modTypings = modifies _2

getSynonyms :: Typecheck [Synonym]
getSynonyms = gets _1

modSynonyms :: ([Synonym] -> [Synonym]) -> Typecheck ()
modSynonyms = modifies _1

tellJudgement :: Judgement -> Typecheck ()
tellJudgement = tell . (<> "\n") . show

retFrac :: Frac -> Typecheck (Type, Frac)
retFrac frac@(Frac _ j _) = do
  tellJudgement j
  pure (ty j, frac)
retFrac frac@(FracIntro _ j) = do
  tellJudgement j
  pure (ty j, frac)

tellLatex :: Latex -> Typecheck ()
tellLatex = lift . lift . tell . (: [])

normalizeType :: Type -> Typecheck (Type, Kind)
normalizeType ty = do
  synonyms <- getSynonyms
  case normalize synonyms [] ty of
    Right p -> pure p
    Left e -> throwError e

-- | Check a type is closed and of kind v'Type'.
checkWellType :: Type -> Typecheck ()
checkWellType ty = do
  (tyN, k) <- normalizeType ty
  case k of
    Type -> pure ()
    _ -> throwError $ "type mismatch: " <> show tyN <> " : " <> show k <> " is not of kind *"

isNFEqual :: Type -> Type -> Typecheck Bool
isNFEqual ty1 ty2 = do
  -- It's impossible for these two type to have a kind other than *.
  ty1' <- normalizeType ty1
  ty2' <- normalizeType ty2
  pure (ty1' == ty2')

whnfType' :: TypeContext -> Type -> Typecheck Type
whnfType' vs ty = do
  synonyms <- getSynonyms
  case whnf synonyms vs ty of
    Just ty -> pure ty
    Nothing -> throwError $ "type mismatch: " <> show ty <> " is a malformed type"

whnfType :: Type -> Typecheck Type
whnfType = whnfType' []

maybeModalType :: Type -> Typecheck (Maybe Type)
maybeModalType ty = do
  tyW <- whnfType ty
  case tyW of
    Mu v ty -> do
      tyW <- whnfType' [(v, Type)] ty
      case tyW of
        ty :*: TypeVar s | v == s -> do
          -- To make sure that 'ty' does not contain 'v'
          synonyms <- getSynonyms
          pure $ case normalize synonyms [] ty of
            Right _  -> Just ty
            Left _ -> Nothing
        _ -> pure Nothing
    _ -> pure Nothing

locate :: AST -> Typecheck a -> Typecheck a
locate ast action = catchError action (\e -> throwError (e <> "\nin " ++ show ast))

typecheck :: AST -> Typecheck (Type, Frac)
typecheck ast@(Lam var ty body) = locate ast $ do
  checkWellType ty
  inc <- getContext
  (ty', premise) <- withAddition var ty $ typecheck body
  out <- getContext
  retFrac $ Frac [premise] (Judgement inc out ast (ty :->: ty')) LolipopI
typecheck ast@(App f x) = locate ast $ do
  inc <- getContext
  (fTy, fPremise) <- typecheck f
  (xTy, xPremise) <- typecheck x
  out <- getContext
  fTyW <- whnfType fTy
  case fTyW of
    ty :->: ty' -> do
      b <- ty `isNFEqual` xTy
      unless b $ throwError $ "type mismatch: can't apply " <> show f <> " : " <> show fTy <> " to " <> show x <> " : " <> show xTy
      retFrac $ Frac [fPremise, xPremise] (Judgement inc out ast ty') LolipopE
    _ -> throwError $ "type mismatch: " <> show f <> " : " <> show fTy <> " is not of a function type"
typecheck ast@(Var var) = locate ast $ do
  inc <- getContext
  case filter (\(a, _, _) -> a == var) inc of
    (_, i, ty) : _ -> do
      removeFromCtx i
      out <- getContext
      retFrac $ Frac [] (Judgement inc out ast ty) Nil
    [] -> throwError $ "variable not found or used up in context: " <> var
typecheck ast@(Call var) = locate ast $ do
  inc <- getContext
  global <- getTypings
  case lookup var global of
    Just ty -> do
      let out = inc
      retFrac $ FracIntro (var, ty) (Judgement inc out ast ty)
    Nothing -> throwError $ "term name not found in global terms: " <> var
typecheck ast@(Tensor a b) = locate ast $ do
  inc <- getContext
  (aTy, aPremise) <- typecheck a
  (bTy, bPremise) <- typecheck b
  out <- getContext
  retFrac $ Frac [aPremise, bPremise] (Judgement inc out ast (aTy :*: bTy)) TensorI
typecheck ast@(LetTensor a b t body) = locate ast $ do
  inc <- getContext
  (tTy, tPremise) <- typecheck t
  tTyW <- whnfType tTy
  case tTyW of
    aTy :*: bTy -> do
      (ty, premise) <- withAddition a aTy $ withAddition b bTy $ typecheck body
      out <- getContext
      retFrac $ Frac [tPremise, premise] (Judgement inc out ast ty) TensorE
    _ -> throwError $ "type mismatch: " <> show t <> " : " <> show tTy <> " is not of a tensor type"
typecheck ast@Star = locate ast $ do
  inc <- getContext
  let out = inc
  retFrac $ Frac [] (Judgement inc out ast One) OneI
typecheck ast@(Inl bTy a) = locate ast $ do
  checkWellType bTy
  inc <- getContext
  (aTy, premise) <- typecheck a
  out <- getContext
  retFrac $ Frac [premise] (Judgement inc out ast (aTy :+: bTy)) TensorI
typecheck ast@(Inr aTy b) = locate ast $ do
  checkWellType aTy
  inc <- getContext

  (bTy, premise) <- typecheck b
  out <- getContext
  retFrac $ Frac [premise] (Judgement inc out ast (aTy :+: bTy)) TensorI
typecheck ast@(CasePlus x a ma b mb) = locate ast $ do
  inc <- getContext
  (xTy, premise) <- typecheck x
  xTyW <- whnfType xTy
  case xTyW of
    aTy :+: bTy -> do
      backup <- getContext
      (maTy, maPremise) <- withAddition a aTy $ typecheck ma
      context1 <- getContext
      putContext backup
      (mbTy, mbPremise) <- withAddition b bTy $ typecheck mb
      context2 <- getContext
      let out = context1 `intersect` context2
      putContext out
      b <- maTy `isNFEqual` mbTy
      if b
        then retFrac $ Frac [premise, maPremise, mbPremise] (Judgement inc out ast (min maTy mbTy)) PlusE
        else throwError $ "type mismatch: " <> show ma <> " : " <> show maTy <> " and " <> show mb <> " : " <> show mbTy <> " are not of the same type"
    _ -> throwError $ "type mismatch: " <> show x <> " : " <> show xTy <> " is not of a sum type"
typecheck ast@(Absurd ty a) = locate ast $ do
  checkWellType ty
  inc <- getContext
  (aTy, premise) <- typecheck a
  aTyW <- whnfType aTy
  case aTyW of
    Zero -> do
      out <- getContext
      retFrac $ Frac [premise] (Judgement inc out ast ty) ZeroE
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not of type 0"
typecheck ast@(With a b) = locate ast $ do
  inc <- getContext
  (aTy, premise) <- typecheck a
  context1 <- getContext
  putContext inc
  (bTy, premise') <- typecheck b
  context2 <- getContext
  let out = context1 `intersect` context2
  putContext out
  retFrac $ Frac [premise, premise'] (Judgement inc out ast (aTy :&: bTy)) WithI
typecheck ast@(Fst a) = locate ast $ do
  inc <- getContext
  (aTy, premise) <- typecheck a
  aTyW <- whnfType aTy
  case aTyW of
    ty :&: _ -> do
      out <- getContext
      retFrac $ Frac [premise] (Judgement inc out ast ty) WithEL
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not of a with type"
typecheck ast@(Snd a) = locate ast $ do
  inc <- getContext
  (aTy, premise) <- typecheck a
  aTyW <- whnfType aTy
  case aTyW of
    _ :&: ty -> do
      out <- getContext
      retFrac $ Frac [premise] (Judgement inc out ast ty) WithER
    _ -> throwError $ "type mismatch: " <> show a <> " : " <> show aTy <> " is not of a with type"
typecheck ast@(Fold ty body) = locate ast $ do
  checkWellType ty
  tyW <- whnfType ty
  case tyW of
    Mu v t -> do
      let expanded = expand (Just ty) v t
      inc <- getContext
      (tyBody, premise) <- typecheck body
      out <- getContext
      b <- expanded `isNFEqual` tyBody
      if b
        then retFrac $ Frac [premise] (Judgement inc out ast ty) MuI
        else throwError $ "type mismatch: " <> show body <> " : " <> show tyBody <> " is not of type " <> show expanded
    _ -> throwError $ "type mismatch: " <> show ty <> " is not a recursive type"
typecheck ast@(Unfold body) = locate ast $ do
  inc <- getContext
  (ty, premise) <- typecheck body
  out <- getContext
  tyW <- whnfType ty
  case tyW of
    Mu v t -> do
      let expanded = expand (Just ty) v t
      retFrac $ Frac [premise] (Judgement inc out ast expanded) MuE
    _ -> throwError $ "type mismatch: " <> show ty <> " is not a recursive type"
typecheck ast@(Fix v ty body) = locate ast $ do
  checkWellType ty
  maybeTy <- maybeModalType ty
  case maybeTy of
    Just innerTy -> do
      inc <- getContext
      incN <- sequence $ (\(v, _, t) -> (,(v, t)) <$> maybeModalType t) <$> inc
      case lookup Nothing incN of
        Nothing -> do
          i <- serial
          modContext ((v, i, ty) :)
          (ty', premise) <- typecheck body
          b <- innerTy `isNFEqual` ty'
          if b
            then retFrac $ Frac [premise] (Judgement inc [] ast (min innerTy ty')) ByFix
            else throwError $ "type mismatch: " <> show body <> " : " <> show ty' <> " is not of type " <> show innerTy
        Just (v, t) -> throwError $ "type mismatch: current context contains non-modal type " <> v <> " : " <> show t
    Nothing -> throwError $ "type mismatch: " <> show ty <> " is not a modal type"

typecheckSource :: Source -> Typecheck Interface
typecheckSource [] = pure []
typecheckSource (TypeDecl v ty : decls) = do
  synonyms <- getSynonyms
  case normalize synonyms [] ty of
    Right (tyN, k) -> do
      let syn = (v, (ty, tyN, k))
      modSynonyms (syn :)
      tell $ show syn <> "\n\n"
      tellLatex $ LatexSynonym syn
      ress <- typecheckSource decls
      pure $ TypeProto syn : ress
    Left e -> throwError $ e <> "\nin the definition of " <> v
typecheckSource (TermDecl v ast : rest) = do
  tell $ v <> ": \n"
  (ty, frac) <- catchError (typecheck ast) $ \e ->
    throwError $ e <> "\nin the definition of type " <> v
  tell "\n"
  tellLatex $ LatexFrac frac
  let typing = (v, ty)
  modTypings (typing :)
  ress <- typecheckSource rest
  pure $ TermProto typing : ress

-- runCheck :: AST -> IO ()
-- runCheck e = do
--   let (eth, log) = evalRWS (runExceptT (typecheck e)) () ([], [], [], 0)
--   putStrLn log
--   case eth of
--     Left err -> putStrLn ("Error: " <> err)
--     Right (t, frac) -> do
--       putStrLn $ show e <> " : " <> show t <> "\n"
--       putStrLn (showLatex frac)

runCheckSource :: Source -> IO ()
runCheckSource src = do
  let ((eth, log), latexes) = evalState (runWriterT (runWriterT (runExceptT (typecheckSource src)))) ([], [], [], 0)
  putStrLn "Code:\n"
  print src
  putStrLn "Log:\n"
  putStrLn log
  case eth of
    Left err -> putStrLn ("Error: " <> err)
    Right interface -> do
      putStrLn "Latex:\n"
      print latexes
      putStrLn "Interface:\n"
      print interface
      putStrLn "HVM:\n"
      print $ traslateSrc src
