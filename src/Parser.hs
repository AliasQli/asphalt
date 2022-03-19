{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

module Parser where

import Text.Megaparsec
import Data.Text ( Text )
import qualified Data.Text as T
import Data.Void
import Text.Megaparsec.Char
import Data.Functor
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Char

import AST

type Parser = Parsec Void Text

lexeme :: Parser a -> Parser a
lexeme = L.lexeme hspace

symbol :: Text -> Parser Text
symbol = L.symbol hspace

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comment :: Parser ()
comment = hspace >> L.skipLineComment "--"

emptyline :: Parser ()
emptyline = hspace >> char '\n' $> ()

emptyblock :: Parser ()
emptyblock = void $ many $ try emptyline <|> comment

name :: Parser Text
name = lexeme $ do
  c <- upperChar
  cs <- takeWhileP Nothing isLetter
  pure (c `T.cons` cs)

typeName :: Parser Text
typeName = lexeme $ do
  c <- upperChar <|> char '!' <|> char '?'
  cs <- takeWhileP Nothing isLetter
  pure (c `T.cons` cs)

variable :: Parser Text
variable = lexeme $ do
  let reserved = ["let", "in", "inl", "inr", "fst", "snd", "case" , "of", "absurd", "fold", "unfold", "fix"]
  c <- lowerChar
  cs <- takeWhileP Nothing isLetter
  let r = c `T.cons` cs
  if r `elem` reserved
    then fail $ "reserved word " <> show r
    else pure r

data Operator a
  = InfixL (Parser (a -> a -> a))
  | InfixR (Parser (a -> a -> a))
  | Prefix (Parser (a -> a))

makeExprParser :: [[Operator a]] -> Parser a -> Parser a
makeExprParser = flip $ foldl addPrecLevel
  where
    addPrecLevel term ops = do
      let (ls, rs, pre) = foldr filterOperator ([], [], []) ops
      x <- pTerm (choice pre) term
      choice [pInfixR (choice rs) term x, pInfixL (choice ls) term x, pure x]
    
    filterOperator (InfixL f) (ls, rs, pre) = (f:ls, rs, pre)
    filterOperator (InfixR f) (ls, rs, pre) = (ls, f:rs, pre)
    filterOperator (Prefix f) (ls, rs, pre) = (ls, rs, f:pre)

    pTerm pre term = do
      f <- option id pre
      x <- term
      pure (f x)
    
    pInfixL op p x = do
      f <- op
      y <- p
      let r = f x y
      pInfixL op p r <|> pure r
    
    pInfixR op p x = do
      f <- op
      y <- p >>= \r -> pInfixR op p r <|> pure r
      pure (f x y)

parseKind :: Parser Kind
parseKind = makeExprParser
  [[InfixR $ try $ symbol "->" $> (:->>)]] $
      try (parens parseKind)
  <|> symbol "*" $> Type

parseType :: Parser Type
parseType = makeExprParser
  [ [InfixL $ pure (:.:)]
  , [InfixL $ try $ symbol "&" $> (:&:), InfixL $ try $ (symbol "⊗" <|> symbol "*") $> (:*:)]
  , [InfixR $ try $ (symbol "⊕" <|> symbol "+") $> (:+:)]
  , [InfixR $ try $ (symbol "⊸" <|> symbol "->") $> (:->:)]
  ] $ choice
  [ try (parens parseType)
  , try parseMu
  , try parseLam
  , symbol "1" $> One
  , symbol "0" $> Zero
  , try $ TypeCall <$> typeName
  , try $ TypeVar <$> variable
  ]
  where
    parseMu = do
      try (symbol "μ ") <|> symbol "@ "
      v <- variable
      symbol "."
      t <- parseType
      pure (Mu v t)
    parseLam = do
      symbol "λ" <|> symbol "\\"
      (v, k) <- parens $ do
        v <- variable
        symbol ":"
        k <- parseKind
        pure (v, k)
      symbol "."
      t <- parseType
      pure (TypeLam v k t)

parseParenType :: Parser Type
parseParenType = choice
  [ symbol "1" $> One
  , symbol "0" $> Zero
  , try $ TypeCall <$> typeName
  , try $ TypeVar <$> variable
  , parens parseType
  ]

parseSynonym :: Parser Synonym
parseSynonym = do
  symbol "type "
  name <- typeName
  symbol "="
  t <- parseType
  symbol "↪" <|> symbol "=>"
  tN <- parseType
  symbol ":"
  k <- parseKind
  pure (name, (t, tN, k))

parseTyping :: Parser Typing
parseTyping = do
  name <- name
  symbol ":"
  t <- parseType
  pure (name, t)

parsePrototype :: Parser Prototype
parsePrototype = try (TermProto <$> parseTyping) <|> TypeProto <$> parseSynonym

parseInterface :: Parser Interface
parseInterface = do
  emptyblock
  sepEndBy parsePrototype emptyblock <* eof

parseAST :: Parser AST
parseAST = makeExprParser
  [ [ InfixL $ pure App
    , Prefix $ try $ Inl <$> (symbol "inl " *> parseParenType)
    , Prefix $ try $ Inr <$> (symbol "inr " *> parseParenType)
    , Prefix $ try $ symbol "fst " $> Fst
    , Prefix $ try $ symbol "snd " $> Snd
    , Prefix $ try $ Absurd <$> (symbol "absurd " *> parseParenType)
    , Prefix $ try $ Fold <$> (symbol "fold " *> parseParenType)
    , Prefix $ try $ symbol "unfold " $> Unfold
    ]
  , [InfixL $ try $ (symbol "⊗" <|> symbol "*") $> Tensor, InfixL $ try $ symbol "&" $> With]
  ] $ choice
  [ try (parens parseAST)
  , try parseFix
  , try parseLam
  , try parseLet
  , try parseCase
  , try $ symbol "*" $> Star
  , try $ Var <$> variable
  , try $ Call <$> name
  ]
  where
    parseLam = do
      symbol "λ" <|> symbol "\\"
      (v, ty) <- parens $ do
        v <- variable
        symbol ":"
        ty <- parseType
        pure (v, ty)
      symbol "."
      b <- parseAST
      pure (Lam v ty b)
    parseLet = do
      symbol "let "
      a <- variable
      symbol "⊗" <|> symbol "*"
      b <- variable
      symbol "="
      x <- parseAST
      symbol "in "
      m <- parseAST
      pure (LetTensor a b x m)
    parseCase = do
      symbol "case "
      x <- parseAST
      symbol "of "
      symbol "inl "
      a <- variable
      symbol "->"
      ma <- parseAST
      symbol ";"
      symbol "inr "
      b <- variable
      symbol "->"
      mb <- parseAST
      pure (CasePlus x a ma b mb)
    parseFix = do
      symbol "fix"
      (v, ty) <- parens $ do
        v <- variable
        symbol ":"
        ty <- parseType
        pure (v, ty)
      symbol "."
      body <- parseAST
      pure (Fix v ty body)

parseDecl :: Parser Decl
parseDecl = try parseTypeDecl <|> parseTermDecl
  where
    parseTypeDecl = do
      symbol "type "
      name <- typeName
      symbol "="
      t <- parseType
      pure (TypeDecl name t)
    parseTermDecl = do
      name <- name
      symbol "="
      x <- parseAST
      pure (TermDecl name x)

parseSource :: Parser Source
parseSource = do
  emptyblock
  sepEndBy parseDecl emptyblock <* eof

interface :: Text
interface = "type Nat = μ a. 1 ⊕ a ↪ μ a. 1 ⊕ a : *\n\
\type ! = λ(b : *). μ a. b ⊗ a ↪ λ (b : *). μ a. b ⊗ a : * -> *\n\
\type X = ! Nat ↪ μ a. (μ a. 1 ⊕ a) ⊗ a : *\n\
\Zero : Nat\n\
\Succ : Nat ⊸ Nat--niknm\n\
\ --- nk\n\
\Pred : Nat ⊸ Nat\n\
\Plus : Nat ⊸ Nat ⊸ Nat\n\
\One : Nat\n\
\Two : Nat\n\
\Three : Nat\n\
\Ifte : 1 ⊕ 1 ⊸ Nat & Nat ⊸ Nat\n\
\Not : 1 ⊕ 1 ⊸ 1 ⊕ 1\n\
\NANP : Nat ⊸ Nat & Nat\n\
\Main : Nat"

source :: Text
source = "type Nat = μ a. 1 ⊕ a\n\
\type ! = λ (b : *). μ a. b ⊗ a\n\
\type X = ! Nat\n\
\Zero = fold Nat (inl Nat *)\n\
\Succ = λ (x : Nat). fold Nat (inr 1 x)\n\
\Pred = λ (x : Nat). case unfold x of inl s -> Zero; inr n -> n\n\
\Plus = fix (p : ! (Nat ⊸ Nat ⊸ Nat)). λ (x : Nat). λ (y : Nat). case unfold x of inl s -> y; inr n -> let rec ⊗ q = (unfold p) in Succ (rec n y)\n\
\One = Succ Zero\n\
\Two = Succ One\n\
\Three = Succ Two\n\
\Ifte = λ (b : 1 ⊕ 1). λ (n : Nat & Nat). case b of inl x -> fst n; inr y -> snd n\n\
\Not = λ (b : 1 ⊕ 1). case b of inl x -> inr 1 *; inr y -> inl 1 *\n\
\NANP = λ (n : Nat). n & Succ n\n\
\Main = Ifte (Not (inl 1 *)) (NANP Two)"
