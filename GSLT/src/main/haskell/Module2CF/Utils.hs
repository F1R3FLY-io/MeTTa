module Utils
  ( wordsWhen
  , splitUnderscores
  , joinUnderscores
  , isTerminal
  ) where

import Data.List ( intercalate )
import MettaVenus.Abs

-- | Splits a string based on a predicate.
wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'

-- | Splits a string on underscores.
splitUnderscores :: String -> [String]
splitUnderscores s = wordsWhen (=='_') s

-- | Joins a list of strings with underscores.
joinUnderscores :: [String] -> String
joinUnderscores = intercalate "_"

-- | Checks whether an Item is a terminal.
isTerminal :: Item -> Bool
isTerminal (Terminal _) = True
isTerminal _            = False
