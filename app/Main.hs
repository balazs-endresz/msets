{-# LANGUAGE GHC2021          #-}
{-# LANGUAGE LexicalNegation  #-}
{-# LANGUAGE OverloadedLists  #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}

-- This module uses RebindableSyntax, which makes numeric literals and lists
-- have an mset type by default. This way type annotations are usually not necessary.

module Main where

import Data.Ratio
import Data.Semigroup
import GHC.Exts (toList)
import Prelude qualified (fromInteger, (^), (^^))
import Prelude hiding (fromInteger, (^), (^^))

import Msets
import Multiplicity
import Show
import Tests

-- Numeric literals are msets by default in this file, so we get 0::Int some other way.
-- Apply succ/pred to izero to get other numbers.
izero = fromIntegral (maxBound - maxBound :: Int)

-- msets-specific replacements for typeclass methods to make RebindableSyntax work:
fromList :: [Mset a] -> Mset (Mset a)
fromList (x:xs) = Cons x (fromList xs)
fromList _      = Zero
fromListN _ = fromList

fromInteger :: Integer -> Mset (Mset a)
fromInteger n | n >= izero = fromList $ replicate (Prelude.fromInteger n) Zero
              | n <  izero = neg $ fromInteger -n

x ^  y = (Prelude.^ ) x (toInteger @IntM y)
x ^^ y = (Prelude.^^) x (toInteger @IntM y)

-- values have Mset types by default without type signatures
x0 = 0
x1 = [1]
x2 = [[2]]

-- list syntax pattern matching works for msets too
sqroot [[x,y]] | x == y = [[x]]

-- We have NoMonomorphismRestriction here to allow pointfree functions
-- without explicit type signatures. (This might change later)
-- ghci> showAlpha' $ d $ 2*α^3
-- 6α²
-- d :: IsMset a => Mset (Mset a) -> Mset (Mset a)
d = sum . fmap (\x -> upcast x * [x-1])

main = tests
