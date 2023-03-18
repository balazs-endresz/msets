{-# LANGUAGE GHC2021          #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE LexicalNegation  #-}

-- This module uses RebindableSyntax, which makes numeric literals and lists
-- have an mset type by default. This way type annotations are usually not necessary.

module Main where
import Prelude qualified (fromInteger)
import Prelude hiding (fromListN, fromInteger)
import GHC.Exts (toList)  -- required for list syntax pattern matching
import Msets

izero = fromIntegral (maxBound - maxBound :: Int)
-- succ/pred izero to get other numbers

fromList :: [Mset a] -> Mset (Mset a)
fromList (x:xs) = Cons x (fromList xs)
fromList _      = Zero
fromListN _ = fromList

fromInteger :: Integer -> Mset (Mset a)
fromInteger n | n >= izero = fromList $ replicate (Prelude.fromInteger n) Zero
              | n <  izero = neg $ fromInteger -n

x0 = 0
x1 = [1]
x2 = [[2]]

sqroot [[x,y]] | x == y = [[x]]

main = tests
