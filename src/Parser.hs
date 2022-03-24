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

import Data

type Parser = Parsec Void Text

spaces :: Parser ()
spaces = try $ space <* many (L.skipLineComment "--" >> space)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaces

symbol :: Text -> Parser Text
symbol = L.symbol spaces

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

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
  cs <- takeWhileP Nothing isAlphaNum
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
  [ [InfixL $ pure TApp]
  , [InfixL $ try $ symbol "&" $> (:&:), InfixL $ try $ (symbol "⊗" <|> symbol "*") $> (:*:)]
  , [InfixR $ try $ (symbol "⊕" <|> symbol "+") $> (:+:)]
  , [InfixR $ try $ (symbol "⊸" <|> symbol "->") $> (:->)]
  ] $ choice
  [ try (parens parseType)
  , try parseTMu
  , try parseLam
  , symbol "1" $> One
  , symbol "0" $> Zero
  , try $ TCall <$> typeName
  , try $ TVar <$> variable
  ]
  where
    parseTMu = do
      try (symbol "μ ") <|> symbol "@ "
      v <- variable
      symbol "."
      t <- parseType
      pure (TMu v t)
    parseLam = do
      symbol "λ" <|> symbol "\\"
      (v, k) <- parens $ do
        v <- variable
        symbol ":"
        k <- parseKind
        pure (v, k)
      symbol "."
      t <- parseType
      pure (TLam v k t)

parseParenType :: Parser Type
parseParenType = choice
  [ symbol "1" $> One
  , symbol "0" $> Zero
  , try $ TCall <$> typeName
  , try $ TVar <$> variable
  , parens parseType
  ]

parseSynonym :: Parser Synonym
parseSynonym = choice
  [ do
    symbol "type "
    name <- typeName
    symbol "="
    t <- parseType
    symbol ":"
    k <- parseKind
    pure (name, Syn t k)
  , do
    symbol "data "
    name <- typeName
    symbol ":"
    k <- parseKind
    pure (name, Data k)
  ]

parseTyping :: Parser Typing
parseTyping = do
  name <- name
  symbol ":"
  t <- parseType
  pure (name, t)

parsePrototype :: Parser Prototype
parsePrototype = try (TermProto <$> parseTyping) <|> SynProto <$> parseSynonym

parseInterface :: Parser Interface
parseInterface = do
  spaces
  sepEndBy parsePrototype (symbol ";") <* eof

parseAST :: Parser AST
parseAST = makeExprParser
  [ [ InfixL $ pure App
    , Prefix $ try $ symbol "inl " $> Inl
    , Prefix $ try $ symbol "inr " $> Inr
    , Prefix $ try $ symbol "fst " $> Fst
    , Prefix $ try $ symbol "snd " $> Snd
    , Prefix $ try $ symbol "absurd " $> Absurd
    , Prefix $ try $ Fold <$> (symbol "fold " *> parseParenType)
    , Prefix $ try $ Unfold' <$> (symbol "unfold " *> parseParenType)
    , Prefix $ try $ symbol "unfold " >> symbol "_ " $> Unfold
    ]
  , [InfixL $ try $ (symbol "⊗" <|> symbol "*") $> Tensor, InfixL $ try $ symbol "&" $> With]
  ] $ choice
  [ try (parens parseAST)
  , try parseFix
  , try parseLam
  , try parseLet
  , try parseCase
  , try $ symbol "tt" $> Unit
  , try $ Var <$> variable
  , try $ Call <$> name
  ]
  where
    parseLam = do
      symbol "λ" <|> symbol "\\"
      v <- variable
      symbol "."
      b <- parseAST
      pure (Lam v b)
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
      symbol "|"
      symbol "inr "
      b <- variable
      symbol "->"
      mb <- parseAST
      pure (CasePlus x a ma b mb)
    parseFix = do
      symbol "fix"
      v <- variable
      symbol "."
      body <- parseAST
      pure (Fix v body)

parseDecl :: Parser Decl
parseDecl = try parseTypeDecl <|> try parseDataDecl <|> try parseTermDecl <|> parseTermDeclTyped
  where
    parseTypeDecl = do
      symbol "type "
      name <- typeName
      symbol "="
      t <- parseType
      pure (TypeDecl name t)
    parseDataDecl = do
      symbol "data "
      name <- typeName
      symbol ":"
      k <- parseKind
      pure (DataDecl name k)
    parseTermDecl = do
      name <- name
      symbol "="
      x <- parseAST
      pure (TermDecl name x)
    parseTermDeclTyped = do
      name <- name
      symbol ":"
      t <- parseType
      symbol "="
      x <- parseAST
      pure (TermDeclTyped name x t)

parseSource :: Parser Source
parseSource = do
  spaces
  sepEndBy parseDecl (symbol ";") <* eof
