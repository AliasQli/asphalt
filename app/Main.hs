{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import System.Environment
import qualified Data.Text.IO as T
import Text.Megaparsec
import Control.Monad
import System.Exit
import System.FilePath
import Data.Text (Text)

import AST
import Parser
import Latex
import HVM (runtime)

main :: IO ()
main = do
  args <- getArgs
  let process log latex exec args = case args of
        "-v" : as -> process True log exec as
        "-l" : as -> process log True exec as
        "-e" : as -> process log latex True as
        [file] -> run log latex exec file []
        file : "-i" : is -> run log latex exec file is
        _ -> putStrLn "Usage: asphalt [OPTIONS] file [-i interface1 interface2 ...]\nOptions: -l for latex, -v for log, -e for executable hvm file. -i to load interfaces."
  process False False False args

runtimeHVM :: Text
runtimeHVM = $(runtime)

run :: Bool -> Bool -> Bool -> String -> [String] -> IO ()
run log latex exec file is = do
  f <- T.readFile file
  case parse parseSource file f of
    Left e -> putStrLn (errorBundlePretty e) >> exitWith (ExitFailure 1)
    Right source -> do
      ihs <- forM is $ \nm -> do
        f <- T.readFile nm
        hvm <- T.readFile (replaceExtension file "hvmp")
        case parse parseInterface nm f of
          Left e -> putStrLn (errorBundlePretty e) >> exitWith (ExitFailure 1)
          Right i -> return ((nm, i), hvm <> "\n")
      let (is, hvms) = unzip ihs
      let (log', eth) = runCheckSource is source
      when log $ putStrLn "Log:\n" >> T.putStrLn log'
      case eth of
        Left e -> T.putStrLn e
        Right (interface, src, latexes) -> do
          when latex $ putStrLn "Latex:\n" >> printText latexes
          T.writeFile (replaceExtension file "aphi") (text interface)
          T.writeFile (replaceExtension file "hvmp") (text src)
          when exec $ T.writeFile (replaceExtension file "hvm") (runtimeHVM <> mconcat hvms <> text src)
