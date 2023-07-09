{-# LANGUAGE GHC2021           #-}
{-# LANGUAGE LexicalNegation   #-}

module Multiplicity where

import Data.Ratio

-- Each element of an mset has a Multiplicity, which is either One or any number,
-- e.g. `Mul (3%2)`, where we can pass anything with a `Num` instance to the `Mul` constructor.
-- 3%2 is a rational number, or rational mset when RebindableSyntax is on.
-- `One` is needed to construct integer msets.
-- There's a Num Multiplicity instance to make it easier to add/subtract these values directly.
data Multiplicity where
  One :: Multiplicity
  Mul :: (Real m, Show m, Eq m, Ord m) => m -> Multiplicity  -- `Num m` doesn't work here

instance Show Multiplicity where
  show One = "1"
  show (Mul r)
   | denominator (toRational r) == 1 = show . numerator . toRational $ r
   | otherwise = show r
-- TODO:
-- ghci> Mul (2%3)
-- 2 % 3
-- ghci> 2/3
-- • No instance for (Fractional (Mset (Mset ())))

instance Eq Multiplicity where
  One   == One   = True
  One   == Mul r = 1 == r
  Mul r == One   = r == 1
  Mul r == Mul s = toRational r == toRational s

instance Ord Multiplicity where
  compare One     One     = EQ
  compare One     (Mul r) = compare 1 r
  compare (Mul r) One     = compare r 1
  compare (Mul r) (Mul s) = compare (toRational r) (toRational s)

instance Num Multiplicity where
  One   + One   = Mul 2
  One   + Mul r = Mul (1+r)
  Mul r + One   = Mul (r+1)
  Mul r + Mul s = Mul (toRational r + toRational s)

  One   * One   = Mul 1
  One   * Mul r = Mul r
  Mul r * One   = Mul r
  Mul r * Mul s = Mul (toRational r * toRational s)

  negate One     = Mul -1
  negate (Mul r) = Mul -r

  fromInteger = Mul . fromInteger

  abs One     = 1
  abs (Mul r) = Mul (abs r)

  signum One     = 1
  signum (Mul r) = Mul (signum r)
