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

-- fromMset can be used safely with numeric literals but is a partial function for general msets
-- fromMset :: Num b => Mset (Mset a) -> b
fromMset AntiZero      = error "Can't convert -0 to Int or Integer"
fromMset x | isAnti x  = negate $ fromMset (neg x)
           | isInt  x  = fromIntegral . length $ x
           | otherwise = error "Only an mset of empty msets can be converted to Int or Integer"
msetToInt     x = fromMset x :: Int
msetToInteger x = fromMset x :: Integer

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
