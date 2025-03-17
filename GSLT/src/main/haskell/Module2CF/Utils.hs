-- | Utility functions for string manipulation and item checking.
module Utils
  ( wordsWhen
  , splitUnderscores
  , joinUnderscores
  , isTerminal
  ) where

import Data.List ( intercalate )
import MettaVenus.Abs

-- | Splits a string based on a predicate.
-- This is a generic splitting function that breaks the string whenever the predicate holds.
wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'

-- | Splits a string on underscore characters.
splitUnderscores :: String -> [String]
splitUnderscores s = wordsWhen (=='_') s

-- | Joins a list of strings using underscores as the separator.
joinUnderscores :: [String] -> String
joinUnderscores = intercalate "_"

-- | Checks whether a grammar item is a terminal.
-- An item is considered terminal if it matches the 'Terminal' constructor.
isTerminal :: Item -> Bool
isTerminal (Terminal _) = True
isTerminal _            = False
