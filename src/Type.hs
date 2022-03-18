{-# LANGUAGE FlexibleInstances #-}

module Type where

import Latex
import Control.Monad

type Var = String
type Name = String

data Kind
  = Type
  | Kind :->> Kind
  deriving Eq

instance Show Kind where
  showsPrec _ Type = showString "*"
  showsPrec d (a :->> b) = showParen (d > 5) $ showsPrec 6 a . showString " -> " . showsPrec 5 b

instance ShowLatex Kind where
  showsLatexPrec _ Type = showString "*"
  showsLatexPrec d (a :->> b) = showParen (d > 5) $ showsLatexPrec 6 a . showString " \\to " . showsLatexPrec 5 b

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
infixr 5 :->:
infix 6 :*:
infix 6 :+:
infix 6 :&:

instance Show Type where
  showsPrec _ One = showString "1"
  showsPrec _ Zero = showString "0"
  showsPrec _ (TypeVar v) = showString v
  showsPrec _ (TypeCall n) = showString n
  showsPrec d (t1 :->: t2) = showParen (d > 5) $ showsPrec 6 t1 . showString " ⊸ " . showsPrec 5 t2
  showsPrec d (t1 :*: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " ⊗ " . showsPrec 7 t2
  showsPrec d (t1 :+: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " ⊕ " . showsPrec 7 t2
  showsPrec d (t1 :&: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " & " . showsPrec 7 t2
  showsPrec d (Mu v t) = showParen (d > 1) $ showString "μ " . showString v . showString ". " . showsPrec 1 t
  showsPrec d (TypeLam v k t2) = showParen (d > 1) $ showString "λ (" . showString v . showString " : " . shows k . showString "). " . shows t2
  showsPrec d (t1 :.: t2) = showParen (d > 10) $ showsPrec 10 t1 . showString " " . showsPrec 11 t2

instance ShowLatex Type where
  showsLatexPrec _ One = showString "\\bold{1}"
  showsLatexPrec _ Zero = showString "\\bold{0}"
  showsLatexPrec _ (TypeVar v) = showString v
  showsLatexPrec _ (TypeCall n) = showString n
  showsLatexPrec d (t1 :->: t2) = showParen (d > 5) $ showsLatexPrec 6 t1 . showString " \\multimap " . showsLatexPrec 5 t2
  showsLatexPrec d (t1 :*: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\otimes " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :+: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\oplus " . showsLatexPrec 7 t2
  showsLatexPrec d (t1 :&: t2) = showParen (d > 6) $ showsLatexPrec 7 t1 . showString " \\& " . showsLatexPrec 7 t2
  showsLatexPrec d (Mu v t) = showParen (d > 1) $ showString "\\mu " . showString v . showString " . \\space " . showsLatexPrec 1 t
  showsLatexPrec d (TypeLam v k t2) = showParen (d > 1) $ showString "\\lambda (" . showString v . showString  " : " . showsLatexPrec 0 k . showString "). \\space " . showsLatexPrec 1 t2
  showsLatexPrec d (t1 :.: t2) = showParen (d > 10) $ showsLatexPrec 10 t1 . showString " \\space " . showsLatexPrec 11 t2

type Normalized = Type

type TypeContext = [(Name, Kind)]

type Synonym = (Name, (Type, Normalized, Kind))

instance {-# Overlapping #-} Show Synonym where
  show (nm, (ty, nf, kind)) = "type " <> nm <> " = "  <> show ty <> " ↪ " <> show nf <> " : " <> show kind

instance ShowLatex Synonym where
  showsLatexPrec _ (nm, (ty, nf, kind)) =
    showString "\\text{type } " . showString nm . showString " = " . showsLatexPrec 0 ty .
    showString " \\hookrightarrow " . showsLatexPrec 0 nf . showString " : " . showsLatexPrec 0 kind

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

addLeftLocale :: Type -> Either String a -> Either String a
addLeftLocale _ (Right a) = Right a
addLeftLocale t (Left s) = Left $ s <> "\nin type " <> show t

normalize :: [Synonym] -> TypeContext -> Type -> Either String (Normalized, Kind)
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
  unless (k1 == Type) $ Left $ "type " <> show t1 <> " : " <> show k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> show t2 <> " : " <> show k2 <> " is not of kind *"
  pure (t1' :->: t2', Type)
normalize ss vs ty@(t1 :*: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> show t1 <> " : " <> show k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> show t2 <> " : " <> show k2 <> " is not of kind *"
  pure (t1' :*: t2', Type)
normalize ss vs ty@(t1 :+: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> show t1 <> " : " <> show k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> show t2 <> " : " <> show k2 <> " is not of kind *"
  pure (t1' :+: t2', Type)
normalize ss vs ty@(t1 :&: t2) = addLeftLocale ty $ do
  (t1', k1) <- normalize ss vs t1
  unless (k1 == Type) $ Left $ "type " <> show t1 <> " : " <> show k1 <> " is not of kind *"
  (t2', k2) <- normalize ss vs t2
  unless (k2 == Type) $ Left $ "type " <> show t2 <> " : " <> show k2 <> " is not of kind *"
  pure (t1' :&: t2', Type)
normalize ss vs ty@(Mu v t) = addLeftLocale ty $ do
  (t', k) <- normalize ss ((v, Type) : vs) t
  unless (k == Type) $ Left $ "type " <> show t <> " : " <> show k <> " is not of kind *"
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
        else Left $ "can't apply type-level function " <> show t1 <> " : " <> show k1 <> " to " <> show t2 <> " : " <> show k2
    _           -> Left $ "type " <> show t1 <> " : " <> show k1 <> " is not a type-level function"

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
