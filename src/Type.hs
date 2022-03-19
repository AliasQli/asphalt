{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Type where

import Latex
import Control.Monad
import Data.Text (Text)

type Var = Text
type Name = Text

data Kind
  = Type
  | Kind :->> Kind
  deriving (Eq, Show)

instance ShowText Kind where
  textPrec _ Type = showText "*"
  textPrec d (a :->> b) = showTextParen (d > 5) $ textPrec 6 a . showText " -> " . textPrec 5 b

instance ShowLatex Kind where
  showsLatexPrec _ Type = showText "*"
  showsLatexPrec d (a :->> b) = showTextParen (d > 5) $ showsLatexPrec 6 a . showText " \\to " . showsLatexPrec 5 b

data Type
  = One
  | Zero
  | TypeVar Var
  | TypeCall Name
  | Type :->: Type
  | Type :*: Type
  | Type :+: Type
  | Type :&: Type
  | Mu Var Type
  | TypeLam Var Kind Type
  | Type :.: Type
  deriving (Show)
infixr 5 :->:
infix 7 :*:
infix 6 :+:
infix 7 :&:

instance ShowText Type where
  textPrec _ One = showText "1"
  textPrec _ Zero = showText "0"
  textPrec _ (TypeVar v) = showText v
  textPrec _ (TypeCall n) = showText n
  textPrec d (t1 :->: t2) = showTextParen (d > 5) $ textPrec 6 t1 . showText " ⊸ " . textPrec 5 t2
  textPrec d (t1 :*: t2)  = showTextParen (d > 7) $ textPrec 8 t1 . showText " ⊗ " . textPrec 8 t2
  textPrec d (t1 :+: t2)  = showTextParen (d > 6) $ textPrec 7 t1 . showText " ⊕ " . textPrec 7 t2
  textPrec d (t1 :&: t2)  = showTextParen (d > 7) $ textPrec 8 t1 . showText " & " . textPrec 8 t2
  textPrec d (Mu v t) = showTextParen (d > 1) $ showText "μ " . showText v . showText ". " . textPrec 1 t
  textPrec d (TypeLam v k t2) = showTextParen (d > 1) $ showText "λ (" . showText v . showText " : " . textPrec 0 k . showText "). " . textPrec 0 t2
  textPrec d (t1 :.: t2) = showTextParen (d > 10) $ textPrec 10 t1 . showText " " . textPrec 11 t2

instance ShowLatex Type where
  showsLatexPrec _ One = showText "\\bold{1}"
  showsLatexPrec _ Zero = showText "\\bold{0}"
  showsLatexPrec _ (TypeVar v) = showText v
  showsLatexPrec _ (TypeCall n) = showText n
  showsLatexPrec d (t1 :->: t2) = showTextParen (d > 5) $ showsLatexPrec 6 t1 . showText " \\multimap " . showsLatexPrec 5 t2
  showsLatexPrec d (t1 :*: t2) = showTextParen (d > 7) $ showsLatexPrec 8 t1 . showText " \\otimes " . showsLatexPrec 8 t2
  showsLatexPrec d (t1 :+: t2) = showTextParen (d > 6) $ showsLatexPrec 7 t1 . showText " \\oplus " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :&: t2) = showTextParen (d > 7) $ showsLatexPrec 8 t1 . showText " \\& " . showsLatexPrec 8 t2
  showsLatexPrec d (Mu v t) = showTextParen (d > 1) $ showText "\\mu " . showText v . showText " . \\space " . showsLatexPrec 1 t
  showsLatexPrec d (TypeLam v k t2) = showTextParen (d > 1) $ showText "\\lambda (" . showText v . showText  " : " . showsLatexPrec 0 k . showText "). \\space " . showsLatexPrec 1 t2
  showsLatexPrec d (t1 :.: t2) = showTextParen (d > 10) $ showsLatexPrec 10 t1 . showText " \\space " . showsLatexPrec 11 t2

type Normalized = Type

type TypeContext = [(Name, Kind)]

type Synonym = (Name, (Type, Normalized, Kind))

instance ShowText Synonym where
  text (nm, (ty, nf, kind)) = "type " <> nm <> " = "  <> text ty <> " ↪ " <> text nf <> " : " <> text kind

instance ShowLatex Synonym where
  showsLatexPrec _ (nm, (ty, nf, kind)) =
    showText "\\text{type } " . showText nm . showText " = " . showsLatexPrec 0 ty .
    showText " \\hookrightarrow " . showsLatexPrec 0 nf . showText " : " . showsLatexPrec 0 kind

whnf :: [Synonym] -> TypeContext -> Type -> Maybe Type
whnf ss vs (t1 :.: t2) = do
  t1' <- whnf ss vs t1
  case t1' of
    TypeLam v _ body -> do
      case subst v t2 body of
        term@(_ :.: _) -> whnf ss vs term
        term -> pure term
    _           -> Nothing
whnf _ vs (TypeVar v) = case lookup v vs of
  Just _  -> Just (TypeVar v)
  Nothing -> Nothing
whnf ss _ (TypeCall n) = case lookup n ss of
  Just (t, _, _) -> whnf ss [] t -- TODO: type synonym out of scope
  Nothing     -> Nothing
whnf _ _ x = Just x

addLeftLocale :: Type -> Either Text a -> Either Text a
addLeftLocale _ (Right a) = Right a
addLeftLocale t (Left s) = Left $ s <> "\nin type " <> text t

normalize :: [Synonym] -> TypeContext -> Type -> Either Text (Normalized, Kind)
normalize _ _ One = Right (One, Type)
normalize _ _ Zero = Right (Zero, Type)
normalize _ vs ty@(TypeVar v) = addLeftLocale ty $ case lookup v vs of
  Just k  -> Right (TypeVar v, k)
  Nothing -> Left $ "type variable not found in context: " <> v
normalize ss _ ty@(TypeCall n) = addLeftLocale ty $ case lookup n ss of
  Just (_, t, k) -> Right (t, k)
  Nothing        -> Left $ "type synonym not found in global synonyms: " <> n
normalize ss vs ty@(t1 :->: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> text t1 <> " : " <> text k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> text t2 <> " : " <> text k2 <> " is not of kind *"
  pure (t1' :->: t2', Type)
normalize ss vs ty@(t1 :*: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> text t1 <> " : " <> text k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> text t2 <> " : " <> text k2 <> " is not of kind *"
  pure (t1' :*: t2', Type)
normalize ss vs ty@(t1 :+: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> text t1 <> " : " <> text k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> text t2 <> " : " <> text k2 <> " is not of kind *"
  pure (t1' :+: t2', Type)
normalize ss vs ty@(t1 :&: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> text t1 <> " : " <> text k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> text t2 <> " : " <> text k2 <> " is not of kind *"
  pure (t1' :&: t2', Type)
normalize ss vs ty@(Mu v t) = addLeftLocale ty $ do
  (t', k) <- normalize ss ((v, Type) : vs) t
  unless (k == Type) $ Left $ "type " <> text t <> " : " <> text k <> " is not of kind *"
  pure (Mu v t', Type)
normalize ss vs ty@(TypeLam v k t) = addLeftLocale ty $ do
  (t', k') <- normalize ss ((v, k) : vs) t
  pure (TypeLam v k t', k :->> k')
normalize ss vs ty@(t1 :.: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  case t1' of
    TypeLam v k t -> do
      (t2', k2) <- normalize ss vs t2
      if k2 == k
        then normalize ss vs (subst v t2' t)
        else Left $ "can't apply type-level function " <> text t1 <> " : " <> text k1 <> " to " <> text t2 <> " : " <> text k2
    _           -> Left $ "type " <> text t1 <> " : " <> text k1 <> " is not a type-level function"

-- | @'subst' v t m@ = @m[v := t]@
subst :: Var -> Type -> Type -> Type
subst _ _ One = One
subst _ _ Zero = Zero
subst v t (TypeVar s)
  | s == v = t
  | otherwise = TypeVar s
subst _ _ (TypeCall n) = TypeCall n
subst v t (ty :->: ty') = subst v t ty :->: subst v t ty'
subst v t (ty :*: ty')  = subst v t ty :*: subst v t ty'
subst v t (ty :+: ty')  = subst v t ty :+: subst v t ty'
subst v t (ty :&: ty')  = subst v t ty :&: subst v t ty'
subst v t (Mu s ty)
  | s /= v = Mu s (subst v t ty)
  | otherwise = Mu s ty
subst v t (TypeLam s k ty)
  | s /= v = TypeLam s k (subst v t ty)
  | otherwise = TypeLam s k ty
subst v t (ty1 :.: ty2) = subst v t ty1 :.: subst v t ty2

-- | @'rename' v w m@ = rename v to w in m
rename :: Var -> Var -> Type -> Type
rename v s = subst v (TypeVar s)

-- Note only normal forms are able to be determined equal.
instance Eq Normalized where
  One  == One  = True
  Zero == Zero = True
  (TypeVar s) == (TypeVar s') = s == s'
  -- TypeCall should not appear in normal forms.
  (ty :->: ty') == (ty1 :->: ty1') = ty == ty1 && ty' == ty1'
  (ty :*: ty')  == (ty1 :*: ty1')  = ty == ty1 && ty' == ty1'
  (ty :+: ty')  == (ty1 :+: ty1')  = ty == ty1 && ty' == ty1'
  (ty :&: ty')  == (ty1 :&: ty1')  = ty == ty1 && ty' == ty1'
  (Mu s ty) == (Mu s' ty') = if s == s'
    then ty == ty'
    else ty == rename s' s ty'
  (TypeLam s k ty) == (TypeLam s' k' ty') = k == k' && if s == s'
    then ty == ty'
    else ty == rename s' s ty'
  ty1 :.: ty2 == ty1' :.: ty2' = ty1 == ty1' && ty2 == ty2'
  _ == _ = False

instance Ord Type where
  a `compare` b = size a `compare` size b
    where
      size :: Type -> Int
      size One = 1
      size Zero = 1
      size (ty :->: ty') = size ty + size ty' + 1
      size (ty :*: ty') = size ty + size ty' + 1
      size (ty :+: ty') = size ty + size ty' + 1
      size (ty :&: ty') = size ty + size ty' + 1
      size (TypeVar _) = 1
      size (TypeCall _) = 1
      size (Mu _ ty) = size ty + 1
      size ((:.:) ty1 ty2) = size ty1 + size ty2 + 1
      size (TypeLam _ _ ty) = size ty + 1

-- | @expand _ v m@ = @m[v := μ v. m]@, that is, the result of expanding @μ v. m@. The first argument is an optional type synonym for @μ v. m@.
expand :: Maybe Type -> Var -> Type -> Type
expand (Just ty) v t = subst v ty t
expand Nothing v t = subst v (Mu v t) t
