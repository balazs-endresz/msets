{-# LANGUAGE GHC2021           #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LexicalNegation   #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TypeFamilies      #-}
-- {-# LANGUAGE PartialTypeSignatures #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore tests #-}

module Msets where

import Control.Applicative
import Control.Exception (catch, ErrorCall)
import Data.Char (isDigit)
import Data.List (group, intercalate)
import Data.Semigroup
import GHC.Exts (IsList(..))
import GHC.Stack (callStack,  prettyCallStack, HasCallStack)
import Unsafe.Coerce (unsafeCoerce)

-- Data
data Mset a = AntiZero | Zero | Cons a (Mset a)
  deriving (Foldable, Functor, Traversable)

-- Type synonyms
type Base = Mset ()  -- Zero, AntiZero
type IntM = Mset Base  -- 1, 2, -1, etc (the type `Int`, `Integer` already exists)
type Poly = Mset IntM
type Multi = Mset Poly

-- ::M can be applied to a mix of all lower level polymorphic values too,
-- without having to be specific about various types in ghci.
-- Unlike `Mset a`, it is a concrete type, which helps avoid ambigous type errors.
-- one = Cons Zero Zero = 0:[] = [0] = 1
-- minusOne = Cons AntiZero Zero = -0:[] = [-0] = -[0] = Cons Zero AntiZero = -1
type M = Mset (Mset (Mset (Mset (Mset (Mset (Mset Multi))))))

-- G is similar to Alpha, but allows higher level types too (up to a point).
-- Use G to declare a general mset. This can be made a concrete type later with e.g. ::M
-- The type annotation can be sometimes removed, depending on the context it's used in.
-- This is needed because OverloadedLists doesn't support defaulting:
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_lists.html#defaulting
-- https://gitlab.haskell.org/ghc/ghc/-/blob/master/testsuite/tests/plugins/defaulting-plugin/DefaultLifted.hs
-- Also, this is not needed for declarations in ghci! Only when trying to show/print it.
-- x :: G
-- x = [1,-[2]]
type G = forall a. (IsMset a) => Mset (Mset (Mset (Mset (Mset (Mset (Mset (Mset (Mset a))))))))

-- Polymorphic type that can be used up to declare generic alpha values (without using them).
-- These can go up to Multi but can be also cast to the higher level concrete types afterwards.
type Alpha = forall a. (IsMset a) => Mset (Mset (Mset a))

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
isInt = all isEmpty

baseOp Zero     Zero     = Zero
baseOp AntiZero AntiZero = Zero
baseOp Zero     AntiZero = AntiZero
baseOp AntiZero Zero     = AntiZero

-- this doesn't check isAnti for any of the containing elements, only at the top level
isAnti Zero        = False
isAnti AntiZero    = True
isAnti (Cons _ xs) = isAnti xs

-- takes the "anti" of the top level only; containing elements are left unchanged
anti Zero        = AntiZero
anti AntiZero    = Zero
anti (Cons x xs) = Cons x (anti xs)

-- shortcut for anti
a = anti

-- takes the "anti" of the immediate children, or the anti of an empty mset
neg Zero = AntiZero
neg AntiZero = Zero
neg x = fmap anti x

-- unlike `neg` this is not defined for empty msets (this might change later)
isNeg Zero     = error "isNeg undefined for empty mset"
isNeg AntiZero = error "isNeg undefined for empty mset"
isNeg x        = all isAnti x

-- filter elements (top level only)
-- filterMset :: (a -> Bool) -> Mset a -> Mset a
filterMset _     Zero        = Zero
filterMset _     AntiZero    = AntiZero
filterMset pred (Cons x xs)
                 | pred x    = Cons x (filterMset pred xs)
                 | otherwise = filterMset pred xs

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
deleteMset x (Cons y ys)
             | x == y    = ys
             | otherwise = Cons y (deleteMset x ys)

-- eliminate mset and anti-mset pairs (top level only)
-- TODO: add recursive variant
eliminate Zero       = Zero
eliminate AntiZero   = AntiZero
eliminate (Cons x xs)
  | anti x `elem` xs = eliminate (deleteMset (anti x) xs)
  | otherwise        = Cons x (eliminate xs)


instance Applicative Mset where
  pure x = Cons x Zero
  fs <*> ys | isAnti fs, isAnti ys = anti fs <*> anti ys
            | isAnti fs            = anti $ anti fs <*> ys
            | isAnti ys            = anti $ fs <*> anti ys
            | Zero <- fs           = Zero
            | (Cons f fs') <- fs   = fmap f ys <> (fs' <*> ys)

-- create a monomorphic function to avoid ambigous type errors (see caret/wedge in IsMset)
liftA2Mset = liftA2 @Mset

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
    compare Zero        (Cons _ xs) = if isAnti xs then GT else LT
    compare (Cons _ xs) Zero        = if isAnti xs then LT else GT
    compare AntiZero    (Cons _ xs) = if isAnti xs then GT else LT
    compare (Cons _ xs) AntiZero    = if isAnti xs then LT else GT
    compare (Cons _ AntiZero) (Cons _ Zero)     = LT
    compare (Cons _ Zero)     (Cons _ AntiZero) = GT
    compare (Cons x xs)   (Cons y ys) = case compare x y of
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
  x == y = eq (eliminate x) (eliminate y) where
    eq Zero     Zero     = True
    eq AntiZero AntiZero = True
    eq (Cons x xs) ys = maybe False (eq xs . flip deleteMset ys . nth ys) (elemIndex x ys)
    eq _           _  = False
    -- re-define list functions for msets:
    nth = (!!) . toList  -- when inlined above this gives a type error -- why?
    elemIndex x xs = go xs 0 where
      go (Cons y ys) i = if x == y then Just i else go ys (i+1)
      go _           _ = Nothing  -- empty

-- Show

showBase Zero     = "0"
showBase AntiZero = "-0"

showMsetAsInt Zero     = showBase Zero
showMsetAsInt AntiZero = showBase AntiZero
showMsetAsInt x | isAnti x  = 'a' : ' ' : showMsetAsInt (anti x)
                | otherwise = show $
    length (filterMset isZero x) - length (filterMset isAntiZero x)

showMsetAsList f xs | isAnti xs = 'a' : ' ' : showMsetAsList f (anti xs)
                    -- | isNeg xs  = '-' : showMsetAsList f (neg xs)  -- TODO
                    | otherwise =  "[" ++  (intercalate "," . map f . toList) xs  ++ "]"

-- Show
instance Show (Mset ()) where
  show = showBase

-- Show
instance (IsMset (Mset a), Ord (Mset a), Show a, Show (Mset a)) => Show (Mset (Mset a)) where
  show Zero     = showBase Zero
  show AntiZero = showBase AntiZero
  show x        = go (prepare x) where
    go x | isInt x   = showMsetAsInt x
         | otherwise = showMsetAsList show x
    prepare = sortMset . eliminate
    -- prepare = id -- use this to show mset without "evaluating" it

-- Show'
class Show' a where
  showCons :: a -> String
  showZeros :: a -> String
  showEmpty :: a -> String

-- Show' () is needed only for the constraints to work out and
-- to avoid code duplication, but it won't ever be called.
instance Show' () where
  showCons = undefined
  showZeros = undefined
  showEmpty = undefined

instance (Show' a) => Show' (Mset a) where
  showCons Zero = "Zero"
  showCons AntiZero = "AntiZero"
  showCons (Cons x y) = "(Cons " ++ showCons x ++ " " ++ showCons y ++ ")"

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

pick list = map ((list !!) . read @Int . return) . show
sub = pick "₀₁₂₃₄₅₆₇₈₉"
sup = pick "⁰¹²³⁴⁵⁶⁷⁸⁹"
alphaSub = ('α':) . sub
alphaSup = ('α':) . sup

-- to be used without RebindableSyntax
alphaI :: Int -> Alpha
alphaI n = [[fromIntegral n]]

-- to be used with RebindableSyntax
alphaM :: (forall a. Mset (Mset a)) -> Alpha
alphaM n = [[n]]

-- assume RebindableSyntax by default
alpha = alphaM
α = alpha

-- TODO: add Integral mset instance to have a single alpha function

-- TODO: define more with template haskell
α₀,α₁,α₂,α₃,α₀²,α₁²,α₂²,α₃² :: Alpha
α₀  = [[0]]   --  α₀ = [1]
α₁  = [[1]]   -- [α₀]
α₂  = [[2]]   -- [α₀²]
α₃  = [[3]]   -- [α₀³]
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
instance (IsMset (Mset a), ShowA (Mset a), ShowA (Mset (Mset a)), Ord (Mset a), Ord a)
         => ShowA (Mset (Mset (Mset a))) where
  -- TODO: rewrite this in a more sensible way
  -- TODO: handle anti-msets correctly, e.g. minus alpha to the minus one
  showAlpha x = plusMinToMin $ showAntiA go (prepare x)
    where
      prepare = sortMsetWith compareA . eliminate
      go x  | isEmpty x      = showBase x
            | isInt x        = showMsetAsInt x
            | maxDepth x < 4 = showSum x  -- Poly and Multi (or generic variants)
            | otherwise      = error "Only up to Multi is supported for alpha expressions"
      showSum = joinMapPlus "+" showProd
      showProd :: Mset (Mset a) -> String
      showProd Zero     = "1"
      showProd AntiZero = "-1"
      showProd x        = joinMapTimes opTimes (alphaSub . length) (sortMset $ eliminate x)
      joinMapPlus  sep f = intercalate sep . map withMul . countOccurrences . fmap (showAntiA f)
      joinMapTimes sep f = intercalate sep . map withExp . countOccurrences . fmap f
      withMul (e,c) | c > 1 && e ==  "1" = show c       -- positive constant
                    | c > 1 && e == "-1" = '-' : show c   -- negative constant
                    | c > 1              = show c ++ e  -- c times alpha sub n (^ c)
                    | otherwise          = e              -- alpha sub n (^ c)
      withExp (e,c) | c > 1     = e ++ (if opExp /= "" then opExp ++ show c else sup c)  -- alpha sub n ^ c
                    | otherwise = e             -- alpha sub n
      -- countOccurrences :: (Ord (Item l), IsList l) => l -> [(Item l, Int)]
      countOccurrences = map (\(x:xs) -> (x, 1 + length xs)) . group . toList
      showAntiA f x | isAnti x  = '-':(removePlus . map flipSigns . f . anti) x
                    | otherwise = f x
        where
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
      -- same as `compare` but moves constants to the front in alpha expressions
      compareA x        Zero     = GT
      compareA x        AntiZero = GT
      compareA Zero     x        = LT
      compareA AntiZero x        = LT
      compareA x        y        = compare x y
      opTimes = ""
      opExp = ""
      -- to render as valid code replace the last two above with:
      -- opTimes = "*"
      -- opExp = "^"


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
  -- `fromList -[]` is not necessary because `-[]` is `negate []`,
  -- so `fromList` will be called before `negate`
  -- `toList AntiZero` is undefined for the same reason.
  -- There's currently no way to make Mset the default instance for [], see:
  -- https://downloads.haskell.org/~ghc/9.4.1-rc1/docs/users_guide/exts/overloaded_lists.html?highlight=defaulting#defaulting

-- Semigroup
-- Concatenate msets (without eliminating anti and non-anti pairs).
instance Semigroup (Mset a) where
  Zero <> y  = y
  x    <> y | isAnti x, isAnti y = anti x <> anti y
            | isAnti x           = anti (anti x <> y)
            | isAnti y           = anti (x <> anti y)
            | (Cons x' xs) <- x  = Cons x' (xs <> y)


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

  -- TODO: These might not make sense for a general mset.
  -- Maybe specifiy them for IntM/isInt only? + eliminate first?
  abs = undefined
  signum = undefined
  -- abs x = if isNeg x then neg x else x
  -- signum Zero     = 0
  -- signum AntiZero = 0
  -- signum x        = if isNeg x then -1 else 1


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
class (a ~ Mset (Elem a)) => IsMset a where
  type Elem a

  plus  :: a -> a -> a
  times :: a -> a -> a
  caret :: a -> a -> a
  (∧)   :: a -> a -> a
  (∧) = caret
  infixr 8 ∧

  minDepth :: (Num b, Ord b) => a -> b
  maxDepth :: (Num b, Ord b) => a -> b

  minus :: a -> a -> a


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
countZ' :: Mset a -> Base
countZ' = countZ
countN' :: Mset (Mset a) -> IntM
countN' = countN
countP' :: Mset (Mset (Mset a)) -> Poly
countP' = countP
countM' :: Mset (Mset (Mset (Mset a))) -> Multi
countM' = countM

-- We have recursive `Mset a` instances for all higher levels, so this might just be safe.
-- e.g. `upcast (2::IntM) + ([3]::Poly)`
upcast :: Mset a -> Mset (Mset a)
upcast = unsafeCoerce

-- x = 2 :: IntM
-- y = [3] :: Poly
-- align x y
-- x + (align y x)  -- runtime error
align :: (IsMset a, IsMset b) => a -> b -> b
align x y | maxDepth x <= maxDepth y = unsafeCoerce x
          | otherwise = error "Apply align to the other value instead"


instance IsMset (Mset ()) where
  type Elem (Mset ()) = ()
  plus = baseOp
  times = baseOp
  caret = baseOp
  minDepth = const 0
  maxDepth = const 0
  minus = baseOp  -- TODO

instance (IsMset (Mset a)) => IsMset (Mset (Mset a)) where
  type Elem (Mset (Mset a)) = (Mset a)

  -- laws for anti-msets, plus, minus: https://www.youtube.com/watch?v=KQ1o_NYhQNA
  plus = (<>)

  times AntiZero AntiZero = Zero
  times AntiZero x        = AntiZero  -- M*-0=-0 if M!=-0
  times x        AntiZero = AntiZero
  times x        y        = liftA2Mset plus x y  -- here liftA2 works too

  -- laws for caret: https://youtu.be/TqKacqHS-fA?t=1789
  -- TODO: rename to wedge? because we have ^ for the ordinary exponentiation built-in
  -- TODO: do we maybe need special rules for minus one too?
  caret AntiZero AntiZero = Zero
  caret AntiZero x        = AntiZero  -- M^-0=-0 if M!=-0 ???
  caret x        AntiZero = AntiZero
  caret x        y        = liftA2Mset times x y
  -- caret x        y        = liftA2 times x y   -- why won't these work???
  -- caret x        y        = liftA2 @Mset times x y

  minDepth Zero     = 0
  minDepth AntiZero = 0
  minDepth x        = 1 + minimum (fmap minDepth x)

  maxDepth Zero     = 0
  maxDepth AntiZero = 0
  maxDepth x        = 1 + maximum (fmap maxDepth x)

  -- negation has some special rules to avoid contradictions like:
  -- (-0 - p)  !=  -(0 + p)
  -- p - 0 = -p  -- this would differ from how normal integers work)
  -- TODO: this hasn't yet been covered in videos, it might change
  minus x        Zero     = x
  minus x        AntiZero = x
  minus Zero     y        = neg y
  minus AntiZero y        = neg y
  minus x        y        = plus x (neg y)

assertEq :: (HasCallStack, Eq a, Show a) => a -> a -> IO ()
assertEq x y | (x == y) && (show x == show y) = putStr "."
             | otherwise = msgStacktraced $ show x ++ "  !=  " ++ show y

infixl 1 ==:
(==:) :: (HasCallStack, Eq a, Show a) => a -> a -> IO ()
(==:) = assertEq

infixl 1 =:
(=:) :: HasCallStack => M -> M -> IO ()
(=:) = assertEq

infixl 1 =@
(=@) :: HasCallStack => M -> String -> IO ()
x =@ y = showAlpha' x ==: y

assertRaises :: Show a => a -> IO ()
assertRaises x = catch (show x `seq` putStrLn "\nFAIL") handler
  where
    handler :: ErrorCall -> IO ()
    handler _ = putStr "."


msgStacktraced :: HasCallStack => String -> IO ()
msgStacktraced msg = putStrLn $ "\nFAIL " ++ fromCallStack callStack ++ ": " ++ msg
  where
    fromCallStack = lineNumber . last . lines . prettyCallStack
    lineNumber = takeWhile (/= ':') . drop 4 . dropWhile (/= '.')

tests = do
  []   =: Zero
  -[]  =: AntiZero
  0    =: Zero
  -0   =: AntiZero
  a [] =: AntiZero
  (-0::M) ==  (0::M) ==: False  -- 0 and -0 shouldn't equal as mests
  (-0::M) === (0::M) ==: False  -- 0 and -0 shouldn't equal as mests
  -0 == 0 ==: True   -- without RebindableSyntax these will default to Int

  [0] + -[]     =: [0] + a []
  [0] + -[]     =: a 1
  [0] + a [0]   =: a 2
  [0] + -[0]    =: 0
  [0] + a -[0]  =: [0] + a [a 0]
  [1] + a [a 0] =: a [1, a 0]

  -(-0) =: 0
  -0    =: a 0
  0+0   =: 0
  0+ -0 =: -0
  -1    =: neg 1
  -[0]  =: [a 0]
  1+1   =: 2
  1+0   =: 1
  1+1   =: 2
  [0]   =: 1
  -[0]  =: -1
  -[-0] =: 1

  1 + -0        =: a 1
  [0] +  -0 + 0 =: a 1
  [0] + a 0 + 0 =: a 1
  -- [2] + -0      =: a [2]
  -- -[1]+[0,0]    =: [-1,0,0]
  [2,[-3]] + -0 =: a [2,[-3]]
  1 * -0        =: -0
  [1]*[1]       =: [2]
  [1,2] * -0    =: -0
  -0 * -0       =:  0
  -0*[1,2]      =: -0
  [1,a 0,0] * [1, a 0,0] =: [2]
  [1, -0,0] * [1,  -0,0] =: [2] -- TODO this should be [2] as well!

  -- negation
  0  -  0 =:  0
  -0 - -0 =: -0
  0  - -0 =:  0
  -0 -  0 =: -0
  1  -  0 =:  1
  0  -  1 =: -1
  1  - -0 =:  1
  -0 -  1 =: -1
  -0 - -1 =:  1

  let x = a [a [1], 2, [], -0]
  let xSquared = [a [0,0,1],a [0,0,1],4,[1,1]]
  xSquared =: x*x

  -- https://youtu.be/TqKacqHS-fA?t=1265
  let c1 = [[1, 2], 4]
  let c2 = [0, [0, 3]]
  c1 ∧ c2 =: [0, [1,4,2,5], 0, [0,0,0,0,3,3,3,3]]

  -- https://youtu.be/TqKacqHS-fA?t=1590
  let c3 = [[1, [2]], [3]]
  let c4 = [2, [1, 3]]
  c3 ∧ c4 =: [ [1,1,[2],[2]], [2,4,[2,0],[2,0,0,0]], [3,3], [4,6] ]

  assertRaises ([1] :: IntM)
  return ([1] :: Poly)  -- no exception

  fmap (*Cons Zero AntiZero) [2,1] =: [a 2,a 1] -- fmap (a 1 *)
  fmap (*Cons AntiZero Zero) [2,1] =: [-1,-2]   -- fmap ( -1 *)
  fmap (+Cons AntiZero Zero) [2,1] =: [1,0]     -- fmap ( -1 +)
  fmap (+Cons Zero AntiZero) [2,1] =: [a 3,a 2] -- fmap (a 1 +)
  fmap id (Cons Zero AntiZero)     =: a 1

  (traverse pure (-[ 1, 2]::M) :: Maybe M) ==: Just -[1,2]
  (traverse pure ( [-1,-2]::M) :: Maybe M) ==: Just [-1,-2]
  (traverse pure ( [-1, 2]::M) :: Maybe M) ==: Just [-1,2]

  filterMset (const True)     [2,1]  =:  [2,1]
  filterMset (const True)    -[2,1]  =: -[2,1]
  filterMset (const False)    [2,1]  =:   0
  filterMset (const False)   -[2,1]  =:   0  -- -[2,1] == [a 2, a 1]
  filterMset (const False) (a [2,1]) =:  -0
  filterMset isEmpty          [2,0]  =:  [0]
  filterMset isZero           [2,0]  =:  [0]
  filterMset isInt    [2,0,[3],-1,0] =:  [2,0,-1,0]

  let x = -[] + [-[1], 2, 3, [], -0]
  let result = [9,6,[a 1,a 1,a 1], 6,4,[a 1,a 1], [a 1,a 1,a 1],[a 1,a 1],[2]]
  x ∧ x =: result
  a [[a 1],2,3] ∧ x =: result
  x ∧ a [[a 1],2,3] =: result
  a [[a 1],2,3] ∧ a [[a 1],2,3] =: result
  [-2,[1]]     ∧ [-2,[1]] =: [-[1,1],-[1,1],4,[2]]
  -[-3,-2,[1]] ∧  0 =:  0
  -[-3,-2,[1]] ∧  1 =: -3
  [-3,-2,[1]]  ∧ -0 =: -0  -- TODO: follow the same rule as multiply?
  -[-3,-2,[1]] ∧ -0 =: -0
  -[1]         ∧ -1 =: -1
  -[1,1]       ∧ -1 =: -2
  -[1,1,1]     ∧ -1 =: -3
  -[1,1,1,1]   ∧ -1 =: -4

  minDepth ([3,[1,[[2]]]]::M) =: 2
  maxDepth ([3,[1,[[2]]]]::M) =: 5

  -- showZeros ([[[-0]]]::M) ==: "[[[-0]]]"
  -- showZeros (-[[[0]]]::M) ==: "-[[[0]]]"

  -- Eq, StrictEq
  ((Cons AntiZero Zero::M) ==  Cons Zero AntiZero) ==: False
  ((Cons AntiZero Zero::M) === Cons Zero AntiZero) ==: False
  ((Cons Zero AntiZero::M) === Cons Zero AntiZero) ==: True

  -- https://www.youtube.com/watch?v=CScJqApRPZg
  α₂         =: [α₀*α₀]
  α₀         =: [1]
  α₀*α₀      =: [2]
  α₀+α₀*α₀   =: [1,2]
  α₁         =: [α₀]
  α₁         =: [[1]]
  2*α₁       =: [α₀, α₀]
  2*α₁       =: [[1],[1]]
  α₁*α₁      =: [α₀+α₀]
  α₁*α₁      =: [[1,1]]
  α₁*α₁*α₁   =: [[1,1,1]]
  α₂         =: [[2]]
  2*α₂       =: α₂+α₂
  2*α₂       =: [[2],[2]]
  α₃         =: [α₀*α₀*α₀]
  α₃         =: [[3]]
  α₁+2*α₂+α₃ =: [[1],[2],[2],[3]]

  [[1],[2],[2],[3]] =@ "α₁+2α₂+α₃"
  [0,[7,2],0] =@ "2+α₂α₇"
  []       =@ "0"
  -[]      =@ "-0"
  [0,-0]   =@ "0"
  [0]      =@ "1"
  -[0]     =@ "-1"
  [0,0]    =@ "2"
  -[0,0]   =@ "-2"
  [0,-0,1] =@ "α₀"

  show (-0::Base) ==: "-0"  -- won't work with RebindableSyntax because 0 is Mset (Mset a)
  show (-0::M)    ==: "-0"
  -- The following works only with RebindableSyntax. Because by default :t +d -0 is Integer.
  -- However, it might also work if LexicalNegation was disabled here:
  -- > Under LexicalNegation, negated literals are desugared without negate.
  -- > That is, -123 stands for fromInteger (-123) rather than negate (fromInteger 123).
  -- TODO: LexicalNegation makes the tests a lot simpler but otherwise it could be dropped.
  -- show (-0)    ==: "-0"

  putStrLn ""