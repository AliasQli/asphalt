{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module AST where

import Data.Text (Text)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Bifunctor
import Control.Effect.Reader
import Control.Effect.Error
import Control.Effect.State
import qualified Data.Text as T
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Carrier.Error.Either
import Data.Functor.Identity
import Control.Monad
import Data.Foldable
import Control.Carrier.Writer.Strict

import Latex
import Type
import Data
import HVM hiding (fold)

default (Text)

inTerm :: Has (Error Text) sig m => AST -> m a -> m a
inTerm ast = locate $ "\nIn " <> text ast

serial :: Has (State Integer) sig m => m Integer
serial = do
  i <- get
  put (i + 1)
  pure i

newvar :: Has (State Integer) sig m => m (Integer, Type)
newvar = do
  n <- get @Integer
  put (n + 1)
  pure (n, TVar $ "t" <> text n)

strip :: Eq b => b -> [(a, b, c)] -> [(a, b, c)]
strip v = filter ((/= v) . mid)

intercalate :: Eq b => [(a, b, c)] -> [(a, b, c)] -> [(a, b, c)]
intercalate [] _ = []
intercalate (x:xs) ys = if any ((== mid x) . mid) ys
  then x : intercalate xs ys
  else intercalate xs ys

data Frac'
  = Frac' [Frac] Type By
  | FracIntro' Typing Type

retFrac' :: Applicative m => Substitution -> Frac' -> m (Substitution, Frac')
retFrac' s (Frac' fracs ty by) = pure (s, Frac' fracs ty by)
retFrac' s (FracIntro' typing ty) = pure (s, FracIntro' typing ty)

toFrac :: (Has (Writer Text) sig m, Has (State Context) sig m) => AST -> m (Substitution, Frac') -> m (Type, Substitution, Frac)
toFrac ast m = do
  inc <- get @Context
  (s, frac') <- m
  out <- get @Context
  case frac' of
    Frac' fracs ty by -> do
      let j = Judgement (subst s inc) (subst s out) ast (subst s ty)
      tell $ text j <> "\n"
      pure (ty, s, Frac fracs j by)
    FracIntro' typing ty -> do
      let j = Judgement (subst s inc) (subst s out) ast (subst s ty)
      tell $ text j <> "\n"
      pure (ty, s, FracIntro typing j)

typeinfer ::
  ( Has (State Integer) sig m
  , Has (Error Text) sig m
  , Has (Reader [Synonym]) sig m
  , Has (Reader [Typing]) sig m
  , Has (State Context) sig m
  , Has (Writer Text) sig m
  ) => AST -> m (Type, Substitution, Frac)
typeinfer ast@(Lam v body) = inTerm ast $ toFrac ast $ do
  (i, t) <- newvar
  modify @Context ((v, i, t) :)
  (ty, s, premise) <- typeinfer body
  modify @Context (strip i)
  retFrac' s $ Frac' [premise] (subst s t :-> ty) LolipopI
typeinfer ast@(App e1 e2) = inTerm ast $ toFrac ast $ do
  (t1, s1, fPremise) <- typeinfer e1

  modify @Context (subst s1)
  (t2, s2, xPremise) <- typeinfer e2

  (_, t) <- newvar
  s3 <- unify t1 (t2 :-> t)
  retFrac' (s3 <> s2 <> s1) $ Frac' [fPremise, xPremise] (subst s3 t) LolipopI
typeinfer ast@(Var v) = inTerm ast $ toFrac ast $ do
  ctx <- get @Context
  case lookup' v ctx of
    Just (i, t) -> do
      modify @Context (strip i)
      retFrac' mempty $ Frac' [] t Nil
    Nothing -> throwError $ "Unbound variable: " <> v
typeinfer ast@(Call nm) = inTerm ast $ toFrac ast $ do
  syns <- ask @[(Name, Type)]
  case lookup nm syns of
    Just t -> do
      let f = Set.toList $ free t
      s <- fmap Map.fromList . forM f $ \v -> do
        (_, t) <- newvar
        pure (v, t)
      retFrac' mempty $ FracIntro' (nm, t) (subst s t)
    Nothing -> throwError $ "Unbound function: " <> nm
typeinfer ast@(Tensor e1 e2) = inTerm ast $ toFrac ast $ do
  (t1, s1, aPremise) <- typeinfer e1

  modify @Context (subst s1)
  (t2, s2, bPremise) <- typeinfer e2

  retFrac' (s2 <> s1) $ Frac' [aPremise, bPremise] (t1 :*: t2) TensorI
typeinfer ast@(LetTensor v1 v2 e1 e2) = inTerm ast $ toFrac ast $ do
  (t1, s1, premise1) <- typeinfer e1

  (ia, ta) <- newvar
  (ib, tb) <- newvar
  s' <- unify t1 (ta :*: tb)

  modify @Context $ ((v1, ia, subst s' ta) :) . ((v2, ib, subst s' tb) :) . subst s1
  (t2, s2, premise2) <- typeinfer e2
  modify @Context $ strip ia . strip ib

  retFrac' (s2 <> s' <> s1) $ Frac' [premise1, premise2] t2 TensorE
typeinfer ast@(Inl e) = inTerm ast $ toFrac ast $ do
  (t, s, premise) <- typeinfer e
  (_, t1) <- newvar
  retFrac' s $ Frac' [premise] (t :+: t1) PlusIL
typeinfer ast@(Inr e) = inTerm ast $ toFrac ast $ do
  (t, s, premise) <- typeinfer e
  (_, t1) <- newvar
  retFrac' s $ Frac' [premise] (t1 :+: t) PlusIR
typeinfer ast@(CasePlus e0 v1 e1 v2 e2) = inTerm ast $ toFrac ast $ do
  (t, s0, premise0) <- typeinfer e0
  modify @Context (subst s0)
  ctx <- get @Context

  (ia, ta) <- newvar
  (ib, tb) <- newvar
  s' <- unify t (ta :+: tb)

  modify @Context ((v1, ia, subst s' ta) :)
  (t1, s1, premise1) <- typeinfer e1
  modify @Context (strip ia)
  ctx1 <- get @Context

  put @Context ctx
  modify @Context $ subst s1 . ((v2, ib, subst s' tb) :)
  (t2, s2, premise2) <- typeinfer e2
  modify @Context (strip ib)
  ctx2 <- get @Context

  put @Context (intercalate ctx1 ctx2)

  s3 <- unify t1 t2
  retFrac' (s3 <> s2 <> s1 <> s' <> s0) $ Frac' [premise0, premise1, premise2] (subst s3 (min t1 t2)) PlusE
typeinfer ast@(With e0 e1) = inTerm ast $ toFrac ast $ do
  ctx <- get @Context
  (t0, s0, premise0) <- typeinfer e0
  ctx1 <- get @Context

  put @Context $ subst s0 ctx
  (t1, s1, premise1) <- typeinfer e1
  ctx2 <- get @Context

  put @Context $ ctx1 `intercalate` ctx2
  retFrac' (s1 <> s0) $ Frac' [premise0, premise1] (t0 :&: t1) WithI
typeinfer ast@(Fst e) = inTerm ast $ toFrac ast $ do
  (t, s, premise) <- typeinfer e
  (_, t1) <- newvar
  (_, t2) <- newvar
  s' <- unify t (t1 :&: t2)
  retFrac' (s' <> s) $ Frac' [premise] (subst s' t1) WithEL
typeinfer ast@(Snd e) = inTerm ast $ toFrac ast $ do
  (t, s, premise) <- typeinfer e
  (_, t1) <- newvar
  (_, t2) <- newvar
  s' <- unify t (t1 :&: t2)
  retFrac' (s' <> s) $ Frac' [premise] (subst s' t2) WithER
typeinfer ast@Unit = inTerm ast $ toFrac ast $ do
  retFrac' mempty $ Frac' [] One OneI
typeinfer ast@(Absurd e) = inTerm ast $ toFrac ast $ do
  (t, s, premise) <- typeinfer e
  s' <- unify t Zero
  (_, t1) <- newvar
  retFrac' (s' <> s) $ Frac' [premise] t1 ZeroE
typeinfer ast@(Fold t e) = inTerm ast $ toFrac ast $ do
  openKindIsType t
  tN <- whnf t
  case tN of
    TMu v t1 -> do
      let t' = subst (Map.singleton v t) t1
      (t2, s, premise) <- typeinfer e
      s' <- unifyTo t2 t'
      retFrac' (s' <> s) $ Frac' [premise] (subst s' t) MuI
    _ -> throwError "cannot fold to a non-recursive type"
typeinfer ast@(Unfold e) = inTerm ast $ toFrac ast $ do
  (t, s, premise) <- typeinfer e
  tN <- whnf t
  case tN of
    TMu v t1 -> do
      let t' = subst (Map.singleton v t) t1
      retFrac' s $ Frac' [premise] t' MuE
    TVar _ -> throwError "cannot unfold a type variable, please use type annotation"
    _ -> throwError "cannot unfold a non-recursive type"
typeinfer ast@(Unfold' t e) = inTerm ast $ toFrac ast $ do
  openKindIsType t
  tN <- whnf t
  case tN of
    TMu v t1 -> do
      let t' = subst (Map.singleton v t) t1
      (t2, s, premise) <- typeinfer e
      s' <- unifyTo t2 t
      retFrac' (s' <> s) $ Frac' [premise] (subst s' t') MuE
    _ -> throwError "cannot unfold a non-recursive type"
typeinfer ast@(Fix v body) = inTerm ast $ toFrac ast $ do
  ctx <- get @Context
  s0 <- fmap fold . forM ctx $ \(_, _, t) -> do
    (_, t1) <- newvar
    unify t (TMu "a" (t1 :*: TVar "a"))
  modify @Context (subst s0)

  (i, t) <- newvar
  modify @Context ((v, i, TMu "a" (t :*: TVar "a")) :)
  (ty, s, premise) <- typeinfer body
  modify @Context (strip i)

  s' <- unify ty t
  retFrac' (s' <> s <> s0) $ Frac' [premise] (subst s' ty) ByFix

typecheck ::
  ( Has (State Integer) sig m
  , Has (Error Text) sig m
  , Has (Reader [Synonym]) sig m
  , Has (Reader [Typing]) sig m
  , Has (State Context) sig m
  , Has (Writer Text) sig m
  ) => Type -> AST -> m (Substitution, Frac)
typecheck ty ast = do
  (ty', s, f) <- typeinfer ast
  s' <- unifyTo ty' ty
  pure (s' <> s, f)

checkNameUnique ::
  ( Has (Error Text) sig m
  , Has (Reader [Typing]) sig m
  ) => Name -> m ()
checkNameUnique name = do
  typings <- ask @[Typing]
  case lookup name typings of
    Nothing -> pure ()
    Just _ -> throwError $ "term " <> name <> " is already defined"

checkTypeNameUnique ::
  ( Has (Error Text) sig m
  , Has (Reader [Synonym]) sig m
  ) => Name -> m ()
checkTypeNameUnique name = do
  synonyms <- ask @[Synonym]
  case lookup name synonyms of
    Nothing -> pure ()
    Just _ -> throwError $ "type " <> name <> " is already defined"

inDef :: Has (Error Text) sig m => Name -> m a -> m a
inDef name = locate $ "\nIn the definition of " <> name

checkSource ::
  ( Has (State Integer) sig m
  , Has (Error Text) sig m
  , Has (Reader [Synonym]) sig m
  , Has (Reader [Typing]) sig m
  , Has (State Context) sig m
  , Has (Writer Text) sig m
  ) => Source -> m (Interface, [Latex])
checkSource [] = pure ([], [])
checkSource (TypeDecl nm ty : s) = do
  k <- inDef nm $ do
    checkTypeNameUnique nm
    closedKind ty
  let syn = (nm, Syn ty k)
  (is, ls) <- local @[Synonym] (syn :) $ checkSource s
  pure (SynProto syn : is, LatexSynonym syn : ls)
checkSource (DataDecl nm k : s) = do
  inDef nm $ checkTypeNameUnique nm
  let syn = (nm, Data k)
  (is, ls) <- local @[Synonym] (syn :) $ checkSource s
  pure (SynProto syn : is, LatexSynonym syn : ls)
checkSource (TermDecl nm ast : s) = do
  (ty, _, f) <- inDef nm $ do
    checkNameUnique nm
    put @Integer 0
    typeinfer ast
  (is, ls) <- local @[Typing] ((nm, ty) :) $ checkSource s
  pure (TermProto (nm, ty) : is, LatexFrac nm f : ls)
checkSource (TermDeclTyped nm ast ty : s) = do
  (_, f) <- inDef nm $ do
    checkNameUnique nm
    put @Integer 0
    typecheck ty ast
  (is, ls) <- local @[Typing] ((nm, ty) :) $ checkSource s
  pure (TermProto (nm, ty) : is, LatexFrac nm f : ls)

inInterface :: Has (Error Text) sig m => String -> m a -> m a
inInterface name = locate $ "\nIn the interface file " <> T.pack name

loadInterface
  :: ( Has (Reader [Synonym]) sig m
     , Has (Reader [Typing]) sig m
     , Has (Error Text) sig m
     )
  => String -> Interface -> m a -> m a
loadInterface _ [] m = m
loadInterface s (SynProto syn@(nm, _) : is) m = do
  inInterface s $ checkTypeNameUnique nm
  local @[Synonym] (syn :) $ loadInterface s is m
loadInterface s (TermProto (nm, ty) : is) m = do
  inInterface s $ checkNameUnique nm
  local @[Typing] ((nm, ty) :) $ loadInterface s is m

runTypeinfer
  :: [Synonym]
  -> [Typing]
  -> ErrorC Text (ReaderC [Synonym] (ReaderC [Typing] (StateC Context (StateC Integer (WriterC Text Identity))))) a
  -> (Text, Either Text a)
runTypeinfer ss ts =
  run .
  runWriter .
  evalState 0 .
  evalState [] .
  runReader ts .
  runReader ss .
  runError

runCheckSource
  :: [(String, Interface)]
  -> Source
  -> (Text, Either Text (Interface, HVMSrc, [Latex]))
runCheckSource sis src = second (second (\(a, b) -> (a, translateSrc src, b))) $ runTypeinfer [] [] (foldr (uncurry loadInterface) (checkSource src) sis)
