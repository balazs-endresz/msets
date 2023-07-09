{-# LANGUAGE GHC2021           #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LexicalNegation   #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE GADTs             #-}

-- {-# LANGUAGE PartialTypeSignatures #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
-- {-# LANGUAGE AllowAmbiguousTypes   #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module Msets where

import Control.Applicative
import Data.Char (isDigit)
import Data.List (group, intercalate)
import Data.Ratio
import Data.Semigroup
import GHC.Exts (IsList(..))
import Unsafe.Coerce (unsafeCoerce)

-- Data
data Mset a = AntiZero
            | Zero
            | ConsMul Multiplicity a (Mset a)
  deriving (Foldable, Functor, Traversable)


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

-- Cons can be used when the multiplicity is one (needed to construct IntM)
pattern Cons :: a -> Mset a -> Mset a
pattern Cons a mset = ConsMul One a mset

-- pattern Succ :: Mset (Mset a) -> Mset (Mset a)
pattern Succ :: IntM -> IntM
pattern Succ mset = Cons Zero mset

-- pattern Pred :: Mset (Mset a) -> Mset (Mset a)
pattern Pred :: IntM -> IntM
pattern Pred mset = Cons AntiZero mset

-- ConsR allows working directly with the Num value, without the Multiplicity its wrapped in.
-- pattern ConsR :: (Real m, Show m, Eq m, Ord m) => m -> a -> Mset a -> Mset a
pattern ConsR mul a mset = ConsMul (Mul mul) a mset


-- Type synonyms
type Base = Mset ()  -- Zero, AntiZero
type IntM = Mset Base  -- 1, 2, -1, etc (the type `Int`, `Integer` already exists)
type Poly = Mset IntM
type Multi = Mset Poly

-- Analogous to: type Rational = Ratio Integer
-- Value can be constructed like 6 % 4, which are normalised.
-- The actual data constructor for Ratio is :% but that can't be used directly.
-- TODO: This type allows for anti-IntM values too, which don't make sense.
type RationalM = Ratio IntM

-- ::M can be applied to a mix of all lower level polymorphic values too,
-- without having to be specific about various types in ghci.
-- Unlike `Mset a`, it is a concrete type, which helps avoid ambigous type errors.
type M = Mset (Mset (Mset (Mset (Mset (Mset (Mset Multi))))))

-- Polymorphic type that can be used up to declare generic alpha values (without using them).
-- These can go up to Multi but can be also cast to the higher level concrete types afterwards.
type Alpha = forall a. (IsMset a) => Mset (Mset (Mset a))

-- The type G works like Alpha but can be applied to more deeply nested msets too.
type G = forall a. (IsMset a) => Mset (Mset (Mset (Mset (Mset (Mset (Mset (Mset (Mset a))))))))


fix x = x :: M

isZero Zero = True
isZero _    = False

isAntiZero AntiZero = True
isAntiZero _        = False

isEmpty Zero     = True
isEmpty AntiZero = True
isEmpty _        = False

-- returns True for [] and -[] too, but using it with Base is a type error
-- isInt :: Mset (Mset a) -> Bool
isInt x = not (isAnti x) && all isEmpty x

baseOp Zero     Zero     = Zero
baseOp AntiZero AntiZero = Zero
baseOp Zero     AntiZero = AntiZero
baseOp AntiZero Zero     = AntiZero

-- this doesn't check isAnti for any of the containing elements, only at the top level
isAnti Zero        = False
isAnti AntiZero    = True
isAnti (ConsMul _ _ xs) = isAnti xs

-- takes the "anti" of the top level only; containing elements are left unchanged
anti Zero        = AntiZero
anti AntiZero    = Zero
-- anti (Cons x xs) = Cons x (anti xs)
anti (ConsMul r x xs) = ConsMul r x (anti xs)

-- shortcut for anti
a = anti

-- takes the "anti" of the immediate children, or the anti of an empty mset
-- TODO: this shouldn't be used for Num!
neg Zero     = AntiZero
neg AntiZero = Zero
neg x        = fmap anti x

-- this is defined for empty msets too (maybe shouldn't be but makes things easier)
isNeg Zero     = False
isNeg AntiZero = True
isNeg x        = all isAnti x

-- filter elements (top level only)
-- filterMset :: (a -> Bool) -> Mset a -> Mset a
filterMset _ Zero     = Zero
filterMset _ AntiZero = AntiZero
filterMset f (Cons x xs)
         | f x        = Cons x (filterMset f xs)
         | otherwise  = filterMset f xs

sortMsetWith cmp mset = if isAnti mset then anti sorted else sorted
  where
    sorted = foldr insertBy [] mset
    insertBy x Zero     = Cons x Zero
    insertBy x AntiZero = Cons x AntiZero
    insertBy x ys@(Cons y ys')
        | cmp x y == GT = Cons y (insertBy x ys')
        | otherwise     = Cons x ys

-- sort elements (top level only)
sortMset :: (Ord a) => Mset a -> Mset a
sortMset = sortMsetWith compare

-- returns a new mset with the first argument removed from it
deleteMset _ Zero        = Zero
deleteMset _ AntiZero    = AntiZero
-- deleteMset x (Cons y ys)
--          | x == y    = ys
--          | otherwise = Cons y (deleteMset x ys)
deleteMset x (ConsMul r y ys)
         | r <  0         = undefined -- expect it to be normalised already
         | r == 0         = ys
         | r == 1, x == y = ys
         | x == y         = ConsMul (r-1) y (deleteMset x ys)
         | otherwise      = ConsMul  r    y (deleteMset x ys)

-- eliminate mset and anti-mset pairs (top level only)
-- TODO: add recursive variant
-- TODO: handle multiplicities properly:  if r > 0
eliminate Zero       = Zero
eliminate AntiZero   = AntiZero
eliminate (ConsMul r x xs)
  | anti x `elem` xs = eliminate (deleteMset (anti x) xs)
  | otherwise        = ConsMul r x (eliminate xs)

-- Ord
instance Ord (Mset ()) where
  compare AntiZero AntiZero = EQ
  compare Zero     Zero     = EQ
  compare AntiZero Zero     = LT
  compare Zero     AntiZero = GT

instance (Ord (Mset a)) => Ord (Mset (Mset a)) where
  compare AntiZero AntiZero = EQ
  compare Zero     Zero     = EQ
  compare AntiZero Zero     = LT
  compare Zero     AntiZero = GT
  compare x@(isInt -> True) y@(isInt -> True)
    | isNeg x, isNeg y = compare (length y) (length x)
    | isNeg x          = LT
    | isNeg y          = GT
    | otherwise        = compare (length x) (length y)
  compare Zero        (Cons _ xs) = if isAnti xs then GT else LT
  compare (Cons _ xs) Zero        = if isAnti xs then LT else GT
  compare AntiZero    (Cons _ xs) = if isAnti xs then GT else LT
  compare (Cons _ xs) AntiZero    = if isAnti xs then LT else GT
  compare (Cons _ AntiZero) (Cons _ Zero)     = LT
  compare (Cons _ Zero)     (Cons _ AntiZero) = GT
  compare (Cons x xs) (Cons y ys) = case compare x y of
      EQ    -> compare xs ys
      other -> if ax == ay then (if ax then compare y x else other) else (if ax then LT else GT)
      where ax = isAnti xs
            ay = isAnti ys


-- StrictEq (exact equality without normalizing msets)
class StrictEq a where
  (===) :: a -> a -> Bool

instance StrictEq (Mset ()) where
  Zero     === Zero     = True
  AntiZero === AntiZero = True
  _        === _        = False

instance (StrictEq (Mset a)) => StrictEq (Mset (Mset a)) where
  Zero       === Zero       = True
  AntiZero   === AntiZero   = True
  (Cons a b) === (Cons c d) = (a === c) && (b === d)
  _          === _          = False


-- Eq (Mset ())
instance Eq (Mset ())  where
  Zero     == Zero     = True
  AntiZero == AntiZero = True
  _        == _        = False

-- Eq (Mset a)
instance (Eq (Mset a)) => Eq (Mset (Mset a)) where
  -- x == y = eq (eliminate $ fmap eliminate x) (eliminate $ fmap eliminate y) where -- TODO
  x == y = eq (eliminate x) (eliminate y) where
    eq Zero     Zero     = True
    eq AntiZero AntiZero = True
    eq (Cons x xs) ys = maybe False (eq xs . flip deleteMset ys . nth ys) (elemIndex x ys)
    eq _           _  = False
    -- re-define list functions for msets:
    nth = (!!) . toList
    elemIndex x xs = go xs 0 where
      go (Cons y ys) i = if x == y then Just i else go ys (i+1)
      go _           _ = Nothing  -- empty

-- Show

showBase Zero     = "0"
showBase AntiZero = "-0"

showMsetAsInt Zero     = showBase Zero
showMsetAsInt AntiZero = showBase AntiZero
showMsetAsInt x
  | isAnti x = "a " ++ showMsetAsInt (anti x)
  | isNeg  x = '-' : showMsetAsInt (neg x)
  | isInt  x = show $ length (filterMset isZero x) - length (filterMset isAntiZero x)

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
  showEmpty AntiZero = "-[]"
  showZeros Zero = "0"
  showZeros AntiZero = "-0"

instance (Show' (Mset a)) => Show' (Mset (Mset a)) where
  showCons Zero = "Zero"
  showCons AntiZero = "AntiZero"
  showCons (Cons x y) = "(Cons " ++ showCons x ++ " " ++ showCons y ++ ")"
  showCons (ConsR r x y) = "(ConsR (" ++ show r ++ ") " ++ showCons x ++ " " ++ showCons y ++ ")"
  showEmpty Zero = "[]"
  showEmpty AntiZero = "-[]"
  showEmpty xs = showMsetAsList showEmpty xs
  showZeros Zero = "0"
  showZeros AntiZero = "-0"
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

alpha n = [[fromIntegral n]] :: Alpha

-- Type signature is required with MonomorphismRestriction only,
-- but if we declare it upfront that makes things easier later.
-- TODO: define more α values with template haskell
α,α₀,α₁,α₂,α₃,α₄,α₅,α₀²,α₁²,α₂²,α₃² :: Alpha
α   = α₀
α₀  = [[0]]   --  α₀ = α = [1]
α₁  = [[1]]   -- [α₀]
α₂  = [[2]]   -- [α₀²]
α₃  = [[3]]   -- [α₀³]
α₄  = [[4]]
α₅  = [[5]]
α₀² = [[0,0]] -- [2]
α₁² = [[1,1]]
α₂² = [[2,2]]
α₃² = [[3,3]]

a0,a1,a2,a3 :: Alpha
a0 = α₀
a1 = α₁
a2 = α₂
a3 = α₃

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
        alphaSubLength x | isNeg x   = alphaSub (-(length x)) ++ "⁻"
                         | otherwise = alphaSub (length x)

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

-- List
-- The list instance is defined for use mainly by the OverloadedLists extension.
-- For everything else, use fmap, filterMset, liftA2Mset, etc instead:
-- these will handle anti-msets correctly.
instance IsList (Mset a) where
  type Item (Mset a) = a
  fromList []        = Zero
  fromList (x:xs)    = Cons x (fromList xs)
  toList Zero        = []
  toList (Cons x xs) = x : toList xs
  -- undefined for fractional multiplicities:
  toList (ConsR r x xs) | denominator (toRational r) == 1 = replicate (toInt r) x ++ toList xs
    where
      toInt = fromInteger . numerator . toRational

  -- `fromList -[]` is not necessary because `-[]` is `negate []`,
  -- so `fromList` will be called before `negate`
  -- `toList AntiZero` is undefined for the same reason.
  -- There's currently no way to make Mset the default instance for [] without RebindableSyntax:
  -- https://downloads.haskell.org/~ghc/9.4.1-rc1/docs/users_guide/exts/overloaded_lists.html?highlight=defaulting#defaulting

-- This helper function takes care of the anti-ness of either msets when
-- they are passed to a binary function. A bit contrived but fun abstraction.
mkBinOp ifZero ifNonZero = go where
  go x y | Zero <- x          = ifZero y
         | isAnti x, isAnti y = anti x `go` anti y
         | isAnti x           = anti (anti x `go` y)
         | isAnti y           = anti (x `go` anti y)
         | (ConsMul r x' xs) <- x = ifNonZero r x' xs y

-- Semigroup
-- Concatenate msets (without eliminating anti and non-anti pairs).
instance Semigroup (Mset a) where
  (<>) = mkBinOp id $ \r x xs ys -> ConsMul r x (xs <> ys)

-- Applicative
instance Applicative Mset where
  pure x = Cons x Zero
  -- TODO: r?
  (<*>) = mkBinOp (const Zero) $ \_r fx fxs ys -> fmap fx ys <> (fxs <*> ys)

-- Create a less polymorphic variant that helps avoid ambigous type errors.
-- Using the same visible type application inline doesn't seem to help in some cases.
liftA2Mset = liftA2 @Mset

-- TODO: try to make these work for polymorphic msets too:
--       • Couldn't match type ‘a1’ with ‘Elem (Mset a1)’
--       • Could not deduce (Elem (Mset a0) ~ a0)

-- Enum (superclass of Integral)
instance (IsMset a, Ord a) => Enum (Mset a) where
  toEnum   = fromIntegral
  fromEnum = assertInt fromIntegral

-- Real (superclass of Integral)
instance (IsMset a, Ord a) => Real (Mset a) where
  toRational = assertInt fromIntegral

-- Integral
instance (IsMset a, Ord a) => Integral (Mset a) where
  quotRem x y = (fromIntegral q, fromIntegral r) where
    (q,r) = quotRem (toInteger x) (toInteger y)
  toInteger = fromIntegral . assertInt toIntegral where
    toIntegral x | isNeg x   = -(toIntegral (neg x))
                 | otherwise = fromIntegral (length x)

assertInt f x = if not (isInt x) then error "non-integer shaped mset" else f x

-- TODO: currently defined only for Poly and above
instance (IsMset a, Ord a) => Fractional (Mset (Mset (Mset a))) where
  -- recip = fmap . fmap anti
  recip x | maxDepth x > 1 = fmap neg x

  -- convert from a Rational value (which is `Ratio Integer`) to mset
  -- fromRational (x :% y) =  fromInteger $ round (fromInteger x / fromInteger y)
  -- This doesn't make sense for Poly but we could define it for int msets that are divisible.
  fromRational = undefined


-- Num (Base)
instance Num (Mset ()) where
  (+) = baseOp
  (*) = baseOp
  negate Zero     = AntiZero
  negate AntiZero = Zero
  fromInteger x | x == 0    = Zero
                | otherwise = error "Specify a higher level Mset type"
  abs    = undefined
  signum = undefined

-- Num (IntM, Poly, etc)
instance IsMset (Mset a) => Num (Mset (Mset a)) where
  (+) = plus
  (-) = minus
  (*) = times
  negate = neg
  fromInteger n | n == 0 = Zero
                | n >  0 = stimes  n (Cons Zero     Zero)
                | n <  0 = stimes -n (Cons AntiZero Zero)

  -- TODO: eliminate
  abs Zero = 0
  abs n
    | not $ isInt n = undefined
    | isNeg n       = neg n
    | otherwise     = n

  signum Zero = 0
  signum n
    | not $ isInt n = undefined
    | isNeg n       = -1
    | otherwise     = 1

-- IsMset
-- This class allows defining operations between:
-- * two concrete msets of the same type (should work as is)
-- * a generic mset and a concrete mset (should work as is)
-- * two concrete msets of different types (use `upcast` to align with the higher level type)
-- * two generic msets (type annotations will be needed at some point, e.g. `::Poly` or even `::M`)
-- Even `Zero` and `AntiZero` can have:
-- * a concrete type `Base`
-- * a generic type `Mset a`
-- * a higher level type `IntM`, `Poly`, `Multi`, etc
class (a ~ Mset (Elem a), Eq a) => IsMset a where
  type Elem a
  plus  :: a -> a -> a
  times :: a -> a -> a
  caret :: a -> a -> a
  (∧)   :: a -> a -> a
  (∧) = caret
  infixr 8 ∧
  minDepth  :: (Num b, Ord b) => a -> b
  maxDepth  :: (Num b, Ord b) => a -> b
  minus     :: a -> a -> a

-- Counting functions: https://youtu.be/TqKacqHS-fA?t=645
-- Unlike the ones in the video these return an anti-mset when applied to an anti-mset
countZ :: Mset a -> Mset b
countZ Zero        = Zero
countZ AntiZero    = AntiZero
countZ (Cons _ xs) = countZ xs
countN :: Mset (Mset a) -> Mset (Mset b)
countN = fmap countZ
countP :: Mset (Mset (Mset a)) -> Mset (Mset (Mset b))
countP = fmap countN
countM :: Mset (Mset (Mset (Mset a))) -> Mset (Mset (Mset (Mset b)))
countM = fmap countP
-- Same functions but with fixed return types:
countZ' = countZ @_ @()
countN' = countN @_ @()
countP' = countP @_ @()
countM' = countM @_ @()

-- We have recursive `Mset a` instances for all higher levels, so this might just be safe.
-- e.g. `upcast (2::IntM) + ([3]::Poly)`
upcast :: Mset a -> Mset (Mset a)
upcast = unsafeCoerce

-- x = 2 :: IntM
-- y = [3] :: Poly
-- y + x          -- type error
-- y + align x y  -- ok
-- x + align y x  -- runtime error
align :: (IsMset a, IsMset b) => a -> b -> b
align x y | maxDepth x <= maxDepth y = unsafeCoerce x
          | otherwise = error "Apply align to the other value instead"


instance IsMset (Mset ()) where
  type Elem (Mset ()) = ()
  plus     = baseOp
  times    = baseOp
  caret    = baseOp
  minDepth = const 0
  maxDepth = const 0
  minus    = baseOp  -- TODO

instance (IsMset (Mset a)) => IsMset (Mset (Mset a)) where
  type Elem (Mset (Mset a)) = (Mset a)

  -- laws for anti-msets, plus, minus: https://www.youtube.com/watch?v=KQ1o_NYhQNA
  plus x y = eliminate $ x <> y

  times AntiZero AntiZero = Zero
  times AntiZero x        = AntiZero  -- M*-0=-0 if M!=-0
  times x        AntiZero = AntiZero
  times x        y        = eliminate $ liftA2 plus x y

  -- laws for caret: https://youtu.be/TqKacqHS-fA?t=1789
  -- TODO: rename to wedge? because we have ^ for the ordinary exponentiation built-in
  -- TODO: do we maybe need special rules for minus one too?
  caret AntiZero AntiZero = Zero
  caret AntiZero x        = AntiZero  -- M^-0=-0 if M!=-0 ???
  caret x        AntiZero = AntiZero
  caret x        y        = eliminate $ liftA2 times x y

  minDepth Zero     = 0
  minDepth AntiZero = 0
  minDepth x        = 1 + minimum (fmap minDepth x)

  maxDepth Zero     = 0
  maxDepth AntiZero = 0
  maxDepth x        = 1 + maximum (fmap maxDepth x)

  minus x y = x `plus` (Cons AntiZero Zero `times` y)  -- x + (-1 * y)
  -- TODO: plus/neg should work too; change definition of neg?
  -- minus x y = plus x (neg y)
