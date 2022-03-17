{-# LANGUAGE FlexibleInstances #-}

module AST where

import Control.Monad

type Var = String

data Kind
  = Type
  | Kind :->> Kind
  deriving Eq

data Type
  = One
  | Zero
  | Type :->: Type
  | Type :*: Type
  | Type :+: Type
  | Type :&: Type
  | TypeVar Var
  | Mu Var Type
  | Type :.: Type
  | TypeLam Var Kind Type
infixr 5 :->:
infix 6 :*:
infix 6 :+:
infix 6 :&:

type Normalized = Type

type Synonyms = [(Var, (Type, Normalized, Kind))]

whnf :: Synonyms -> [(Var, Kind)] -> Type -> Maybe Type
whnf ss vs (t1 :.: t2) = do
  t1' <- whnf ss vs t1
  case t1' of
    TypeLam v _ body -> do
      case subst v t2 body of
        term@(_ :.: _) -> whnf ss vs term
        term -> pure term
    _           -> Nothing
whnf ss vs (TypeVar v) = case lookup v vs of
  Just _ -> Just (TypeVar v)
  Nothing -> case lookup v ss of
    Just (t, _, _) -> Just t
    Nothing     -> Nothing
whnf _ _ x = Just x

normalize :: Synonyms -> [(Var, Kind)] -> Type -> Maybe (Normalized, Kind)
normalize _ _ One = Just (One, Type)
normalize _ _ Zero = Just (Zero, Type)
normalize ss vs (TypeVar v) = case lookup v vs of
  Just k -> Just (TypeVar v, k)
  Nothing -> case lookup v ss of
    Just (_, t, k) -> Just (t, k)
    Nothing     -> Nothing
normalize ss vs (t1 :->: t2) = do
  (t1', Type) <- normalize ss vs t1
  (t2', Type) <- normalize ss vs t2
  pure (t1' :->: t2', Type)
normalize ss vs (t1 :*: t2) = do
  (t1', Type) <- normalize ss vs t1
  (t2', Type) <- normalize ss vs t2
  pure (t1' :*: t2', Type)
normalize ss vs (t1 :+: t2) = do
  (t1', Type) <- normalize ss vs t1
  (t2', Type) <- normalize ss vs t2
  pure (t1' :+: t2', Type)
normalize ss vs (t1 :&: t2) = do
  (t1', Type) <- normalize ss vs t1
  (t2', Type) <- normalize ss vs t2
  pure (t1' :&: t2', Type)
normalize ss vs (Mu v t) = do
  (t', Type) <- normalize ss ((v, Type) : vs) t
  pure (Mu v t', Type)
normalize ss vs (t1 :.: t2) = do
  (t1', _) <- normalize ss vs t1
  case t1' of
    TypeLam v k t -> do
      (t2', a') <- normalize ss vs t2
      guard $ a' == k
      normalize ss vs (subst v t2' t)
    _           -> Nothing
normalize ss vs (TypeLam v k t) = do
  (t', k') <- normalize ss ((v, k) : vs) t
  pure (TypeLam v k t', k :->> k')

subst :: Var -> Type -> Type -> Type
subst _ _ One = One
subst _ _ Zero = Zero
subst v t (ty :->: ty') = subst v t ty :->: subst v t ty'
subst v t (ty :*: ty') = subst v t ty :*: subst v t ty'
subst v t (ty :+: ty') = subst v t ty :+: subst v t ty'
subst v t (ty :&: ty') = subst v t ty :&: subst v t ty'
subst v t (TypeVar s)
  | s == v = t
  | otherwise = TypeVar s
subst v t (Mu s ty)
  | s /= v = Mu s (subst v t ty)
  | otherwise = Mu s ty
subst v t ((:.:) ty1 ty2) = (:.:) (subst v t ty1) (subst v t ty2)
subst v t (TypeLam s k ty)
  | s /= v = TypeLam s k (subst v t ty)
  | otherwise = TypeLam s k ty

rename :: Var -> Var -> Type -> Type
rename v s = subst v (TypeVar s)

instance Eq Normalized where
  One == One = True
  Zero == Zero = True
  (ty :->: ty') == (ty1 :->: ty1') = ty == ty1 && ty' == ty1'
  (ty :*: ty') == (ty1 :*: ty1') = ty == ty1 && ty' == ty1'
  (ty :+: ty') == (ty1 :+: ty1') = ty == ty1 && ty' == ty1'
  (ty :&: ty') == (ty1 :&: ty1') = ty == ty1 && ty' == ty1'
  (TypeVar s) == (TypeVar s') = s == s'
  (Mu s ty) == (Mu s' ty') = if s == s'
    then ty == ty'
    else ty == rename s' s ty'
  ((:.:) ty1 ty2) == ((:.:) ty1' ty2') = ty1 == ty1' && ty2 == ty2'
  (TypeLam s k ty) == (TypeLam s' k' ty') = k == k' && if s == s'
    then ty == ty'
    else ty == rename s' s ty'
  _ == _ = False

size :: Type -> Int
size One = 1
size Zero = 1
size (ty :->: ty') = size ty + size ty' + 1
size (ty :*: ty') = size ty + size ty' + 1
size (ty :+: ty') = size ty + size ty' + 1
size (ty :&: ty') = size ty + size ty' + 1
size (TypeVar _) = 1
size (Mu _ ty) = size ty + 1
size ((:.:) ty1 ty2) = size ty1 + size ty2 + 1
size (TypeLam _ _ ty) = size ty + 1

instance Ord Type where
  a `compare` b = size a `compare` size b

expand :: Maybe Type -> Var -> Type -> Type
expand (Just ty) v t = subst v ty t
expand Nothing v t = subst v (Mu v t) t

data AST
  = Lam Var Type AST              -- λ (Var : Type). AST
  | App AST AST                   -- AST AST
  | Var Var                       -- Var
  | Tensor AST AST                -- AST * AST
  | LetTensor Var Var AST AST     -- let Var * Var = AST in AST
  | Star                          -- *
  | Inl Type AST                  -- inl Type AST
  | Inr Type AST                  -- inr Type AST
  | CasePlus AST Var AST Var AST  -- case AST of inl Var -> AST; inr Var -> AST
  | Absurd Type AST               -- absurd Type AST
  | With AST AST                  -- AST & AST
  | Fst AST                       -- fst AST
  | Snd AST                       -- snd AST
  | Fold Type AST                 -- fold Type AST
  | Unfold AST                    -- unfold AST
  | Fix Var Type AST              -- fix (Var : Type). AST

type Context = [(Var, Int, Type)]

data Decl
  = TypeDecl Var Type
  | TermDecl Var AST

type Source = [Decl]
