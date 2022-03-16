{-# LANGUAGE FlexibleInstances #-}

module ADT where

type Var = String

data Type
  = One
  | Zero
  | Type :->: Type
  | Type :*: Type
  | Type :+: Type
  | Type :&: Type
  deriving (Eq, Ord)
infixr 5 :->:
infix 6 :*:
infix 6 :+:

instance Show Type where
  showsPrec _ One = showString "1"
  showsPrec _ Zero = showString "0"
  showsPrec d (t1 :->: t2) = showParen (d > 5) $ showsPrec 6 t1 . showString " ⊸ " . showsPrec 5 t2
  showsPrec d (t1 :*: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " ⊗ " . showsPrec 7 t2
  showsPrec d (t1 :+: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " ⊕ " . showsPrec 7 t2
  showsPrec d (t1 :&: t2)  = showParen (d > 6) $ showsPrec 7 t1 . showString " & " . showsPrec 7 t2

data ADT
  = Lam Var Type ADT              -- λ(Var : Type). ADT
  | App ADT ADT                   -- ADT ADT
  | Var Var                       -- Var
  | Tensor ADT ADT                -- ADT * ADT
  | LetTensor Var Var ADT ADT     -- let Var * Var = ADT in ADT
  | Star                          -- *
  | Inl Type ADT                  -- inl Type ADT
  | Inr Type ADT                  -- inr Type ADT
  | CasePlus ADT Var ADT Var ADT  -- case ADT of inl Var -> ADT; inr Var -> ADT
  | Absurd Type ADT               -- absurd Type ADT
  | With ADT ADT                  -- ADT & ADT
  | Fst ADT                       -- fst ADT
  | Snd ADT                       -- snd ADT
  deriving (Eq, Ord)

instance Show ADT where
  showsPrec d (Lam v t e) = showParen (d > 0) $
    showString "λ (" . showString v . showString " : " . shows t . showString "). " . shows e
  showsPrec d (App e1 e2) = showParen (d > 10) $
    showsPrec 10 e1 . showString " " . showsPrec 11 e2
  showsPrec _ (Var v) = showString v
  showsPrec d (Tensor e1 e2) = showParen (d > 4) $
    showsPrec 5 e1 . showString " ⊗ " . showsPrec 5 e2
  showsPrec d (LetTensor v1 v2 e1 e2) = showParen (d > 0) $
    showString "let " . showString v1 . showString " ⊗ " . showString v2 . showString " = " . shows e1 . showString " in " . shows e2
  showsPrec _ Star = showString "*"
  showsPrec d (Inl ty e1) = showParen (d > 10) $
    showString "inl " . showsPrec 11 ty . showString " " . showsPrec 11 e1
  showsPrec d (Inr ty e1) = showParen (d > 10) $
    showString "inr " . showsPrec 11 ty . showString " " . showsPrec 11 e1
  showsPrec d (CasePlus e1 v1 e2 v2 e3) = showParen (d > 0) $
    showString "case " . showsPrec 11 e1 . showString " of \
    \inl " . showString v1 . showString " -> " . shows e2 . showString "; \
    \inr " . showString v2 . showString " -> " . shows e3
  showsPrec d (Absurd ty e1) = showParen (d > 10) $
    showString "absurd " . showsPrec 11 ty . showString " " . showsPrec 11 e1
  showsPrec d (With e1 e2) = showParen (d > 4) $
    showsPrec 5 e1 . showString " & " . showsPrec 5 e2
  showsPrec d (Fst e1) = showParen (d > 10) $
    showString "fst " . showsPrec 11 e1
  showsPrec d (Snd e1) = showParen (d > 10) $
    showString "snd " . showsPrec 11 e1

type Context = [(Var, Int, Type)]

instance {-# Overlapping #-} Show Context where
  show [] = "⋅"
  show [(v, _, t)] = v ++ " : " ++ show t
  show ((v, _, t) : ctx) = show ctx ++ ", " ++ v ++ " : " ++ show t

