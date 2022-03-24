{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Type where

import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Bifunctor
import Control.Effect.Reader
import Control.Effect.Error
import Data.Maybe
import qualified Data.Text as T

import Data
import Latex

default (Text)

data Exception
  = TypeException Name TypeException
  | TermException Name TermException

data TypeException
  = InType Type TypeException
  | TypeFuncCantApply Type Kind Type Kind
  | NoTypeFunction Type Kind
  | UnboundTypeVar Var
  | TypeNameNotFound Name
  | KindNotType Type Kind

data TermException
  = InTerm AST TermException
  | EmbedTypeException TypeException
  | UnifyTooGeneral Type Var
  | OccursCheck Var Type
  | CantUnify Type Type

locate :: Has (Error Text) sig m => Text -> m a -> m a
locate t m = catchError m (\e -> throwError (e <> t))

inType :: Has (Error Text) sig m => Type -> m a -> m a
inType t = locate $ "\nIn type " <> text t

kind :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Bool -> Map Var Kind -> Type -> m Kind
kind _ _ (TConst _) = pure Type
kind b m ty@(TOp _ t1 t2) = inType ty $ do
  kindIsType b m t1
  kindIsType b m t2
  pure Type
kind b m ty@(TApp t1 t2) = inType ty $ do
  k1 <- kind b m t1
  k2 <- kind b m t2
  case k1 of
    a :->> b -> do
      if a == k2
        then pure b
        else throwError $ "cannot apply " <> text t1 <> " : " <> text k1 <> " to " <> text t2 <> " : " <> text k2
    _ -> throwError $ "not a type-level function: " <> text t1 <> " : " <> text k1
kind b m ty@(TLam v k t) = inType ty $ do
  k' <- kind b (Map.insert v k m) t
  pure (k :->> k')
kind b m ty@(TMu v t) = inType ty $ do
  kindIsType b (Map.insert v Type m) t
  pure Type
kind b m ty@(TVar v) = inType ty $ case Map.lookup v m of
  Just k -> pure k
  Nothing -> if b 
    then pure Type
    else throwError $ "unbound type variable: " <> v
kind _ _ ty@(TCall n) = inType ty $ do
  ss <- ask @[Synonym]
  case lookup n ss of
    Just (Syn _ k) -> pure k
    Just (Data k)  -> pure k
    Nothing        -> throwError $ "type name not found: " <> n

kindIsType :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Bool -> Map Var Kind -> Type -> m ()
kindIsType b m t = do
  k <- kind b m t
  case k of
    Type -> pure ()
    _    -> throwError $ "not of kind *: " <> text t <> " : " <> text k

closedKind :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Type -> m Kind
closedKind = kind False Map.empty

openKindIsType :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Type -> m ()
openKindIsType = kindIsType True Map.empty

whnf :: (Has (Reader [Synonym]) sig m) => Type -> m Type
whnf (TApp t1 t2) = do
  t1' <- whnf t1
  case t1' of
    TLam v _ body -> do
      case subst (Map.singleton v t2) body of
        term@TApp{} -> whnf term
        term        -> pure term
    _             -> error . T.unpack $ "impossible: not a type-level function: " <> text t1
whnf (TCall n) = do
  ss <- ask @[Synonym]
  case lookup n ss of
    Just (Syn t _) -> whnf t
    Just (Data _)  -> pure $ TCall n
    Nothing        -> error . T.unpack $ "impossible: type name not found: " <> n
whnf x = pure x

unifyPrim :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Bool -> Type -> Type -> m Substitution
unifyPrim _ (TVar v) (TCall n) = pure $ Map.singleton v (TCall n)
unifyPrim b (TCall n) (TVar v) = if b
  then pure $ Map.singleton v (TCall n)
  else throwError $ "cannot unify " <> n <> " to given type variable " <> v <> " which is more general"
unifyPrim _ (TCall n1) (TCall n2)
  | n1 == n2 = pure idSubst
unifyPrim b t1 t2 = do
  t1' <- whnf t1
  t2' <- whnf t2
  unify' t1' t2'
  where
    unify' :: _
    unify' (TOp op t1 t2) (TOp op' t1' t2')
      | op == op' = do
          s1 <- unifyPrim b t1 t1'
          s2 <- unifyPrim b (subst s1 t2) (subst s1 t2')
          pure $ s2 `compose` s1
      | otherwise = throwError $ "cannot unify " <> text (TOp op t1 t2) <> " and " <> text (TOp op' t1' t2') <> " with different operators"
    unify' (TVar a) t
      | t == TVar a = pure idSubst
      | a `elem` free t = throwError $ "occurs check: " <> a <> " in " <> text t
      | otherwise = pure $ Map.singleton a t
    unify' t (TVar a) = if b
      then unify' (TVar a) t
      else throwError $ "cannot unify " <> text t <> " to given type variable " <> a <> " which is more general"
    unify' (TMu v t) (TMu v' t')
      | v == v' = unifyPrim b t t'
      | otherwise = unifyPrim b t (rename v' v t')
    unify' (TConst c) (TConst c')
      | c == c' = pure idSubst
      | otherwise = throwError $ "cannot unify " <> text (TConst c) <> " and " <> text (TConst c')
    unify' (TApp {}) (TApp {}) = error "impossible"
    unify' (TLam {}) (TLam {}) = error "impossible"
    unify' a b = throwError $ "cannot unify " <> text a <> " and " <> text b

unify :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Type -> Type -> m Substitution
unify = unifyPrim True

-- | Usage: @general `unifyTo` specific@
unifyTo :: (Has (Error Text) sig m, Has (Reader [Synonym]) sig m) => Type -> Type -> m Substitution
unifyTo = unifyPrim False

lookup' :: Eq a => a -> [(a, b, c)] -> Maybe (b, c)
lookup' x = go
  where
    go [] = Nothing
    go ((x', b, c) : xs)
      | x == x' = Just (b, c)
      | otherwise = go xs

lft :: (a, b, c) -> a
lft (a, _, _) = a

mid :: (a, b, c) -> b
mid (_, b, _) = b

rgt :: (a, b, c) -> c
rgt (_, _, c) = c

type Substitution = Map Var Type

idSubst :: Substitution
idSubst = Map.empty

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = fmap (subst s1) s2 `Map.union` s1

instance {-# Overlapping #-} Semigroup Substitution where
  (<>) = compose

instance {-# Overlapping #-} Monoid Substitution where
  mempty = idSubst

class Substitutable a where
  subst :: Substitution -> a -> a

instance Substitutable Type where
  subst s (TVar v)       = fromMaybe (TVar v) (Map.lookup v s)
  subst s (TOp op t1 t2) = TOp op (subst s t1) (subst s t2)
  subst s (TApp t1 t2)   = TApp (subst s t1) (subst s t2)
  subst s (TMu v t)      = TMu v (subst (Map.delete v s) t)
  subst s (TLam v k t)   = TLam v k (subst (Map.delete v s) t)
  subst _ t              = t

instance Substitutable Context where
  subst s = fmap (second $ subst s)

rename :: Var -> Var -> Type -> Type
rename v v' = subst $ Map.singleton v (TVar v')

free :: Type -> Set Var
free (TVar v)      = Set.singleton v
free (TOp _ t1 t2) = free t1 `Set.union` free t2
free (TApp t1 t2)  = free t1 `Set.union` free t2
free (TMu v t)     = Set.delete v (free t)
free (TLam v _ t)  = Set.delete v (free t)
free _             = Set.empty
