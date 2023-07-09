{-# LANGUAGE GHC2021           #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LexicalNegation   #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE GADTs             #-}

module Show where

import Data.Char (isDigit)
import Data.List (group, intercalate)
import GHC.Exts (IsList(..))
import Msets


showBase Zero     = "0"
showBase AntiZero = "a 0"

showMsetAsInt Zero     = showBase Zero
showMsetAsInt AntiZero = showBase AntiZero
showMsetAsInt x
  | isAnti x = "a " ++ showMsetAsInt (anti x)
  | isNeg  x = '-' : showMsetAsInt (neg x)
  | isInt  x = show $ length (filterMset isZero x) - length (filterMset isAntiZero x)

showMsetAsList _ Zero     = "[]"
showMsetAsList _ AntiZero = "a []"
showMsetAsList f xs
  | isAnti xs = "a " ++ showMsetAsList f (anti xs)
  | isNeg  xs = '-' : showMsetAsList f (neg xs)
  | otherwise =  "[" ++  (intercalate "," . map f . toList) xs  ++ "]"

-- Show
instance Show (Mset ()) where
  show = showBase

-- Show
instance (IsMset (Mset a), Ord (Mset a), Show a, Show (Mset a)) => Show (Mset (Mset a)) where
  show = go . sortMset . eliminate where
    go x | all isEmpty x = showMsetAsInt x  -- this matches empty msets too
         | otherwise     = showMsetAsList show x

-- Show'
class Show' a where
  showCons :: a -> String
  showZeros :: a -> String
  showEmpty :: a -> String

instance Show' (Mset ()) where
  showCons Zero = "Zero"
  showCons AntiZero = "AntiZero"
  showEmpty Zero = "[]"
  showEmpty AntiZero = "a []"
  showZeros Zero = "0"
  showZeros AntiZero = "a 0"

instance (Show' (Mset a)) => Show' (Mset (Mset a)) where
  showCons Zero = "Zero"
  showCons AntiZero = "AntiZero"
  showCons (Cons x y) = "(Cons " ++ showCons x ++ " " ++ showCons y ++ ")"
  showCons (ConsMul r x y) = "(ConsR (" ++ show r ++ ") " ++ showCons x ++ " " ++ showCons y ++ ")"
  showEmpty Zero = "[]"
  showEmpty AntiZero = "a []"
  showEmpty xs = showMsetAsList showEmpty xs
  showZeros Zero = "0"
  showZeros AntiZero = "a 0"
  showZeros xs = showMsetAsList showZeros xs


-- Render unicode characters like 'α' properly in ghci, and without the qoutes.
-- GHC has `Show Char` and `Show [a]` but we can add a more specific instance for [Char].
-- Note that it also removes qoutes from all num-like strings globally.
-- This can be confusing but it's not an essential behaviour either.
-- It's just for e.g. 0::Alpha, 1::Alpha, etc.
instance {-# OVERLAPPING #-} Show String where
  show x | "" <- x        = "\"\""
         | 'α' `elem` x   = x
         | ('-':xs) <- x
         , all isDigit xs = '-' : xs
         | all isDigit x  = x
         | otherwise      = '"' : x ++ "\""

-- Instead of `Show String` we could use a newtype to render unicode:
newtype PlainString = PlainString String deriving Eq
instance Show PlainString where show (PlainString s) = s

pick list i | i >= 0 = pick' list i
            | i <  0 = '⁻': pick' list (-i)
  where
    pick' list = map ((list !!) . read @Int . return) . show

sup :: (Integral a, Show a) => a -> String
sup = pick "⁰¹²³⁴⁵⁶⁷⁸⁹"
sub :: (Integral a, Show a) => a -> String
sub = pick "₀₁₂₃₄₅₆₇₈₉"
alphaSup = ('α':) . sup
alphaSubM = ('α':) . sub
alphaSubP x | x == 0    = "α"
            | otherwise = 'α': sub x


-- shorthand that applies the concrete type M to the mset
showAlpha' = showAlpha @M

-- ShowA
class ShowA a where
  showAlpha :: a -> String
instance ShowA Base where
  showAlpha = showBase
instance ShowA IntM where
  showAlpha = showMsetAsInt
instance ShowA Poly where
  showAlpha = showAlpha . upcast
instance (IsMset (Mset a), Ord (Mset a), ShowA (Mset (Mset (Mset a))))
         => ShowA (Mset (Mset (Mset (Mset a)))) where
  -- TODO: rewrite this in a more sensible way
  showAlpha x = plusMinToMin $  go (prepare x)
    where
      prepare = sortMsetWith compareA . eliminate
      go x = case maxDepth x of
          0 -> showBase x       -- empty
          1 -> showMsetAsInt x  -- int
          2 -> showSum x        -- poly
          3 -> showSum x        -- multi  -- TODO: not tested with more complex cases yet
          _ -> error "Only up to Multi is supported for alpha expressions"

      showSum x | isAnti x  = brackets $ showSum (anti x)
                | otherwise = joinMapPlus "+" showProd x
        where
          brackets x | ('+' `elem` tail x) || ('-' `elem` tail x) = "a (" ++ x ++ ")"
                     | otherwise = "a " ++ x

      alphaSub = if maxDepth x == 2 then alphaSubP else alphaSubM -- α for poly and α₀ for multi

      showProd Zero     = "1"
      showProd AntiZero = "-1"
      showProd x        = joinMapTimes "" alphaSubLength (sortMset $ eliminate x) where
        alphaSubLength Zero              = alphaSub 0
        alphaSubLength AntiZero          = alphaSub 0 ++ "⁻"
        alphaSubLength x@(isNeg -> True) = alphaSub (-(length x)) ++ "⁻"
        alphaSubLength x                 = alphaSub (length x)

      joinMapPlus  sep f = intercalate sep . map withMul . countOccurrences . fmap (showAntiA f)
      joinMapTimes sep f = intercalate sep . map withExp . countOccurrences . fmap f

      withMul (e,c)
        | e == showBase Zero     = show c           -- positive constant
        | e == showBase AntiZero = '-':show c       -- negative constant
        | c > 1, ('-':e') <- e   = '-':show c ++ e' -- -c times alpha sub n (^ c)
        | c > 1                  = show c ++ e      --  c times alpha sub n (^ c)
        | otherwise              = e                -- alpha sub n (^ c)
      withExp (e,c)
        | c == 1, last e /= '⁻' = e -- alpha sub n ^ 1
        | otherwise             = e ++ sup c  -- alpha sub n ^ c
      -- countOccurrences :: (Ord (Item l), IsList l) => l -> [(Item l, Int)]
      countOccurrences = map (\(x:xs) -> (x, 1 + length xs)) . group . toList
      showAntiA f x | isEmpty x = showBase x
                    | isAnti x  = '-':(removePlus . map flipSigns . f . anti) x
                    | otherwise = f x where
        removePlus ('+':xs) = xs
        removePlus xs       = xs
        flipSigns '+' = '-'
        flipSigns '-' = '+'
        flipSigns c   = c
      -- replace +- and -+ with just -
      plusMinToMin = r "" where
        r start ('-':'+':xs) = r start ('-':xs)
        r start ('+':'-':xs) = r start ('-':xs)
        r start (x:xs)       = r (start ++ [x]) xs
        r start []           = start
      -- don't differentiate anti-msets when sorting because they mean only +/- here
      compareA x y | isAnti x  = compareA (anti x) y
                   | isAnti y  = compareA x (anti y)
                   | otherwise = compare x y

-- render alpha expression as valid haskell code
-- showAlphaH = showAlpha  -- TODO: add *, ^, convert superscripts
