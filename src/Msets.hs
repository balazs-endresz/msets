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

{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Msets where

import Control.Applicative
import Data.Ratio
import Data.Semigroup
import GHC.Exts (IsList(..))
import Unsafe.Coerce (unsafeCoerce)
import Multiplicity

-- Data
data Mset a = AntiZero
            | Zero
            | ConsMul Multiplicity a (Mset a)
  deriving (Foldable, Functor, Traversable)

-- Pattern Synonyms

-- Cons can be used when the multiplicity is One (needed to construct IntM)
pattern Cons :: a -> Mset a -> Mset a
pattern Cons a mset = ConsMul One a mset

-- pattern Succ :: Mset (Mset a) -> Mset (Mset a)
pattern Succ :: IntM -> IntM
pattern Succ mset = Cons Zero mset

-- pattern Pred :: Mset (Mset a) -> Mset (Mset a)
pattern Pred :: IntM -> IntM
pattern Pred mset = Cons AntiZero mset

-- Shorthand to add an element with arbitrary multiplicity:
-- e.g. `ConsR (3%2) Zero Zero` instead of `ConsMul (Mul (3%2)) Zero Zero`
-- TODO: fix type error when pattern signature is commented out
-- pattern ConsR :: (Real m, Show m) => m -> a -> Mset a -> Mset a
pattern ConsR mul a mset = ConsMul (Mul mul) a mset

-- Type synonyms
type Base  = Mset ()    -- Zero, AntiZero
type IntM  = Mset Base  -- 1, 2, -1, etc (the type `Int`, `Integer` already exists)
type Poly  = Mset IntM
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


-- Functions

fix x = x :: M

isZero Zero = True
isZero _    = False

isAntiZero AntiZero = True
isAntiZero _        = False

isEmpty Zero     = True
isEmpty AntiZero = True
isEmpty _        = False

-- returns True for Zero and False for AntiZero, but using it with a Base type is a type error
-- isInt :: Mset (Mset a) -> Bool
isInt x = not (isAnti x) && all isEmpty x

baseOp Zero     Zero     = Zero
baseOp AntiZero AntiZero = Zero
baseOp Zero     AntiZero = AntiZero
baseOp AntiZero Zero     = AntiZero
baseOp _        _        = error "Unexpected non-empty mset"

-- this doesn't check isAnti for any of the containing elements, only at the top level
isAnti Zero             = False
isAnti AntiZero         = True
isAnti (ConsMul _ _ xs) = isAnti xs

-- takes the "anti" of the top level only; containing elements are left unchanged
anti Zero             = AntiZero
anti AntiZero         = Zero
anti (ConsMul r x xs) = ConsMul r x (anti xs)

-- shortcut for anti
a = anti

-- takes the "anti" of the immediate children, leaves empty msets as is
neg = fmap anti

isNeg Zero     = undefined
isNeg AntiZero = undefined
isNeg x        = all isAnti x

-- filter elements (top level only)
-- filterMset :: (a -> Bool) -> Mset a -> Mset a
filterMset _ Zero     = Zero
filterMset _ AntiZero = AntiZero
filterMset f (ConsMul r x xs)
         | f x        = ConsMul r x (filterMset f xs)
         | otherwise  = filterMset f xs

sortMsetWith cmp mset = if isAnti mset then anti sorted else sorted
  where
    sorted = foldr insertBy [] mset
    insertBy x Zero     = Cons x Zero
    insertBy x AntiZero = Cons x AntiZero
    insertBy x ys@(ConsMul r y ys')
        | cmp x y == GT = ConsMul r y (insertBy x ys')
        | otherwise     = Cons x ys

-- sort elements (top level only)
sortMset :: (Ord a) => Mset a -> Mset a
sortMset = sortMsetWith compare

-- returns a new mset with the first argument removed from it
deleteMset _ Zero        = Zero
deleteMset _ AntiZero    = AntiZero
deleteMset x (ConsMul r y ys)
         | r <  0         = deleteMset x $ ConsMul -r (anti y) ys
         | r == 0         = deleteMset x ys
         | r == 1, x == y = ys
         | x == y         = ConsMul (r-1) y (deleteMset x ys)
         | otherwise      = ConsMul  r    y (deleteMset x ys)

-- eliminate mset and anti-mset pairs (top level only)
-- TODO: add recursive variant
eliminate Zero       = Zero
eliminate AntiZero   = AntiZero
eliminate (ConsMul r x xs)
  | r == 0           = eliminate xs
  | r <  0           = eliminate $ ConsMul -r (anti x) xs
  | anti x `elem` xs = eliminate $ deleteMset (anti x) $ ConsMul (r-1) x xs
  | otherwise        = ConsMul r x (eliminate xs)


-- Alpha expressions
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

-- Ord
instance Ord (Mset ()) where
  compare AntiZero AntiZero = EQ
  compare Zero     Zero     = EQ
  compare AntiZero Zero     = LT
  compare Zero     AntiZero = GT
  compare _        _        = error "Unexpected non-empty mset"

instance (Ord (Mset a)) => Ord (Mset (Mset a)) where
  compare AntiZero AntiZero = EQ
  compare Zero     Zero     = EQ
  compare AntiZero Zero     = LT
  compare Zero     AntiZero = GT
  compare x@(isInt -> True) y@(isInt -> True)
    | isNeg' x, isNeg' y = compare (length y) (length x)
    | isNeg' x           = LT
    | isNeg' y           = GT
    | otherwise          = compare (length x) (length y)
    where
      isNeg' Zero     = False
      isNeg' AntiZero = False
      isNeg' x        = isNeg x
  compare Zero        (ConsMul _ _ xs) = if isAnti xs then GT else LT
  compare (ConsMul _ _ xs) Zero        = if isAnti xs then LT else GT
  compare AntiZero    (ConsMul _ _ xs) = if isAnti xs then GT else LT
  compare (ConsMul _ _ xs) AntiZero    = if isAnti xs then LT else GT
  compare (ConsMul _ _ AntiZero) (ConsMul _ _ Zero)     = LT
  compare (ConsMul _ _ Zero)     (ConsMul _ _ AntiZero) = GT
  compare (ConsMul _ x xs) (ConsMul _ y ys) = case compare x y of
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
  Zero             === Zero             = True
  AntiZero         === AntiZero         = True
  (ConsMul r x xs) === (ConsMul s y ys) = (r == s) && (x === y) && (xs === ys)
  _                === _                = False


-- Eq (Mset ())
instance Eq (Mset ())  where
  Zero     == Zero     = True
  AntiZero == AntiZero = True
  _        == _        = False

-- Eq (Mset a)
instance (Eq (Mset a)) => Eq (Mset (Mset a)) where
  x == y = eliminate x `eq` eliminate y where
    Zero     `eq` Zero     = True
    AntiZero `eq` AntiZero = True
    xxs@(ConsMul _ x xs) `eq` yys@(ConsMul _ y ys)
      -- multiplicities are already positive here because of `eliminate`
      | x == y       = deleteMset x xxs == deleteMset y yys
      | x `elem` yys = xs == deleteMset x yys
      | otherwise    = False
    eq _ _ = False


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
  toList (ConsMul (Mul r) x xs) | denominator (toRational r) == 1 = replicate (toInt r) x ++ toList xs
    where
      toInt = fromInteger . numerator . toRational
  toList _ = error "Mset can't be converted to list"

  -- `fromList -[]` is not necessary because `-[]` is `negate []`,
  -- so `fromList` will be called before `negate`
  -- `toList AntiZero` is undefined for the same reason.
  -- There's currently no way to make Mset the default instance for [] without RebindableSyntax:
  -- https://downloads.haskell.org/~ghc/9.4.1-rc1/docs/users_guide/exts/overloaded_lists.html?highlight=defaulting#defaulting

-- This helper function takes care of the anti-ness of either msets
-- when they are passed to a binary function.
mkBinOp ifZero ifNonZero = go where
  go x y | Zero <- x              = ifZero y
         | isAnti x, isAnti y     = anti x `go` anti y
         | isAnti x               = anti (anti x `go` y)
         | isAnti y               = anti (x `go` anti y)
         | (ConsMul r x' xs) <- x = ifNonZero r x' xs y
         | otherwise              = error "mkBinOp: non-exhaustive patterns"

-- Semigroup
-- Concatenate msets (without eliminating anti and non-anti pairs).
instance Semigroup (Mset a) where
  (<>) = mkBinOp id $ \r x xs ys -> ConsMul r x (xs <> ys)

-- Applicative
instance Applicative Mset where
  pure x = Cons x Zero
  -- we expect the multiplicities in the first argument to be all 1 (that's an mset of functions)
  (<*>) = mkBinOp (const Zero) $ \1 f fs ys -> fmap f ys <> (fs <*> ys)


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
  toInteger Zero     = 0
  toInteger AntiZero = undefined
  toInteger x = (fromIntegral . assertInt toIntegral) x where
    toIntegral x | isNeg x   = -(toIntegral (neg x))
                 | otherwise = fromIntegral (length x)

assertInt f x = if not (isInt x) then error "Mset can't be converted to int" else f x

-- TODO: currently defined only for Poly and above
instance (IsMset a, Ord a) => Fractional (Mset (Mset (Mset a))) where
  -- recip = fmap . fmap anti
  recip x | maxDepth x > 1 = fmap neg x
  recip _ = error "Not implemented"

  -- Convert from a Rational value (which is `Ratio Integer`) to an mset.
  -- fromRational (x :% y) = fromInteger $ round (fromInteger x / fromInteger y)
  -- This doesn't make sense for Poly but we could define it for int msets that are divisible.
  fromRational = undefined  -- TODO


-- Num (Base)
instance Num (Mset ()) where
  (+) = baseOp
  (*) = baseOp
  negate = id  -- to be consistent with negating zero, which remains zero
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
  fromInteger _ = error "fromInteger: non-exhaustive patterns"

  -- TODO: eliminate
  abs Zero = 0
  abs AntiZero = undefined
  abs n
    | not $ isInt n = undefined
    | isNeg n       = neg n
    | otherwise     = n

  signum Zero = 0
  signum AntiZero = undefined
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
countZ x = if isAnti x then AntiZero else Zero
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
  minus    = baseOp
  times    = baseOp
  caret    = baseOp
  minDepth = const 0
  maxDepth = const 0

instance (IsMset (Mset a)) => IsMset (Mset (Mset a)) where
  type Elem (Mset (Mset a)) = (Mset a)

  -- laws for anti-msets, plus, minus: https://www.youtube.com/watch?v=KQ1o_NYhQNA
  plus x y = eliminate $ x <> y

  minus x y = plus x (neg y)

  times AntiZero AntiZero = Zero
  times AntiZero x        = AntiZero  -- M*(a 0)=(a 0) if M!=a 0
  times x        AntiZero = AntiZero
  times x        y        = eliminate $ liftA2 plus x y

  -- laws for caret: https://youtu.be/TqKacqHS-fA?t=1789
  -- TODO: rename to wedge? because we have ^ for the ordinary exponentiation built-in
  -- TODO: do we maybe need special rules for minus one too?
  caret AntiZero AntiZero = Zero
  caret AntiZero x        = AntiZero  -- M^(a 0)=(a 0) if M!=(a 0) ???
  caret x        AntiZero = AntiZero
  caret x        y        = eliminate $ liftA2 times x y

  minDepth Zero     = 0
  minDepth AntiZero = 0
  minDepth x        = 1 + minimum (fmap minDepth x)

  maxDepth Zero     = 0
  maxDepth AntiZero = 0
  maxDepth x        = 1 + maximum (fmap maxDepth x)
