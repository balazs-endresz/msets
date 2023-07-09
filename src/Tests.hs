{-# LANGUAGE GHC2021           #-}
{-# LANGUAGE LexicalNegation   #-}
{-# LANGUAGE OverloadedLists   #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore tests #-}

module Tests where

import Control.Exception (catch, ErrorCall)
import GHC.Stack (callStack,  prettyCallStack, HasCallStack)

import Msets
import Show

-- two general values are equal and converted to string the same way
infixl 1 ==:
(==:) :: (HasCallStack, Eq a, Show a) => a -> a -> IO ()
x ==: y | x == y, show x == show y = putStr "."
        | otherwise                = putStrLn msg
  where
    msg = "\nFAIL " ++ line ++ ": " ++ show x ++ " != \n" ++ leftPad ++ show y
    line = takeWhile(/= ':').drop 4.dropWhile(/= '.').last.lines$ prettyCallStack callStack
    leftPad = replicate (7 + length line) ' '

-- two msets are equal and converted to string the same way
infixl 1 =:
(=:) :: HasCallStack => M -> M -> IO ()
(=:) = (==:)

-- an mset is converted to the given expression in alpha
infixl 1 =@
(=@) :: HasCallStack => M -> String -> IO ()
x =@ y = showAlpha' x ==: y

-- expect expression to raise runtime error
assertRaises x = catch @ErrorCall (show x `seq` putStrLn "\nFAIL") (const $ putStr ".")


tests = flip (>>) (putStrLn "") $ do
  []   =: Zero
  -[]  =: Zero  -- this is undefined for Base but for e.g. IntM and above negation won't change the anti-ness
  0    =: Zero
  a 0  =: AntiZero
  a [] =: AntiZero
  (a 0::M) ==  (0::M) ==: False  -- 0 and a 0 shouldn't equal as mests
  (a 0::M) === (0::M) ==: False  -- 0 and a 0 shouldn't equal as mests
  -0 == 0 ==: True   -- without RebindableSyntax these will default to Int
  2 ^ 3 =: 8  -- ordinary exponentiation, not the same as caret/wedge, int exponent only

  -- [0] + -[]     =: [0] + a []  -- these are not equal becayse -[] is not the same as `a []`
  -- [0] + -[]     =: a 1
  [0] + a [0]   =: a 2
  [0] + -[0]    =: 0
  [0] + a -[0]  =: [0] + a [a 0]
  [1] + a [a 0] =: a [1, a 0]

  -(a 0) =: a 0  -- negate AntiZero is still AntiZero for a generic mset, but undefined for Base
  a 0    =: a 0
  0+0    =: 0
  0+ a 0 =: a 0
  -1    =: neg 1
  -[0]  =: [a 0]
  1+1   =: 2
  1+0   =: 1
  1+1   =: 2
  [0]   =: 1
  -[0]  =: -1
  -[a 0] =: 1

  1 + a 0        =: a 1
  [0] +  a 0 + 0 =: a 1
  [0] + a 0 + 0 =: a 1
  -- [2] + a 0      =: a [2]
  -- -[1]+[0,0]    =: [-1,0,0]
  [2,[-3]] + a 0 =: a [2,[-3]]
  1 * a 0        =: a 0
  [1]*[1]        =: [2]
  [1,2] * a 0    =: a 0
  a 0 * a 0      =:   0
  a 0*[1,2]      =: a 0
  [1, a 0,0] * [1, a 0,0] =: [2]
  [1, a 0,0] * [1, a 0,0] =: [2]

  -- negation (NB `a 0` is shorthand for `a 0`, `anti 0`, `AntiZero`)
  0   -   0 =:     0
  a 0 - a 0 =:     0 -- a 0 + (-1 * a 0) = a 0 + (a 0) =   0
  0   - a 0 =:   a 0 --   0 + (-1 * a 0) =   0 + (a 0) = a 0
  a 0 -   0 =:   a 0 -- a 0 + (-1 *   0) = a 0 +    0  = a 0
  -- ^ subtraction with Zero and AntiZero is the same as addition/baseOp
  1   -   0 =:    1
  0   -   1 =:   -1 --   0 + (-1 *   1) =   0 +  (-1) =   -1
  1   - a 0 =: a  1 --   1 + (-1 * a 0) =   1 + (a 0) = a  1
  a 0 -   1 =: a -1 -- a 0 + (-1 *   1) = a 0 +  (-1) = a -1
  a 0 -  -1 =: a  1 -- a 0 + (-1 *  -1) = a 0 +    1  = a  1
  -- ^ AntiZero on either side is same as if it was Zero but makes it an anti-mset

  -- subtraction produces the same result for x+(negate y) and x+(-1*y)
  let x = 5
  let y = 2
  plus x (neg y) =: x `plus` (Cons AntiZero Zero `times` y)

  let x = a [a [1], 2, [], a 0]
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
  filterMset (const False) (a [2,1]) =:  a 0
  filterMset isEmpty          [2,0]  =:  [0]
  filterMset isZero           [2,0]  =:  [0]
  filterMset isInt    [2,0,[3],-1,0] =:  [2,0,-1,0]
  filterMset isInt  [a 2,0,[3],-1,0] =:  [0,-1,0]

  let x = a [] + [-[1], 2, 3, [], a 0]
  let result = [9,6,[a 1,a 1,a 1], 6,4,[a 1,a 1], [a 1,a 1,a 1],[a 1,a 1],[2]]
  x ∧ x =: result
  a [[a 1],2,3] ∧ x =: result
  x ∧ a [[a 1],2,3] =: result
  a [[a 1],2,3] ∧ a [[a 1],2,3] =: result
  [-2,[1]]     ∧ [-2,[1]] =: [-[1,1],-[1,1],4,[2]]
  -[-3,-2,[1]] ∧  0 =:  0
  -[-3,-2,[1]] ∧  1 =: -3
  [-3,-2,[1]]  ∧ a 0 =: a 0  -- TODO: follow the same rule as multiply?
  -[-3,-2,[1]] ∧ a 0 =: a 0
  -[1]         ∧ -1 =: -1
  -[1,1]       ∧ -1 =: -2
  a [1]        ∧ -1 =: a -1
  a [1,1]      ∧ -1 =: a -2

  minDepth ([3,[1,[[2]]]]::M) =: 2
  maxDepth ([3,[1,[[2]]]]::M) =: 5

  -- showZeros ([[[a 0]]]::M) ==: "[[[a 0]]]"
  -- showZeros (-[[[0]]]::M) ==: "-[[[0]]]"

  -- Eq, StrictEq
  ((Cons AntiZero Zero::M) ==  Cons Zero AntiZero) ==: False
  ((Cons AntiZero Zero::M) === Cons Zero AntiZero) ==: False
  ((Cons Zero AntiZero::M) === Cons Zero AntiZero) ==: True

  -- Ord
  ( 1::M) >  0 ==: True
  ( 2::M) >  1 ==: True
  (-1::M) <  0 ==: True
  (-1::M) > -2 ==: True

  -- Show
  show (a 0::Base) ==: "a 0"  -- won't work with RebindableSyntax because 0 is Mset (Mset a)
  show (a 0::M)    ==: "a 0"
  showMsetAsInt ([0,0,0,a 0]::IntM) ==: "2" -- won't work with RebindableSyntax because 0 is already `Mset (Mset a)`
  showMsetAsInt ([0,0,0,a 0]::Poly) ==: "2"
  -- The following works only with RebindableSyntax. Because by default :t +d a 0 is Integer.
  -- However, it might also work if LexicalNegation was disabled here:
  -- > Under LexicalNegation, negated literals are desugared without negate.
  -- > That is, -123 stands for fromInteger (-123) rather than negate (fromInteger 123).
  -- TODO: LexicalNegation makes the tests a lot simpler but otherwise it could be dropped.
  -- show (a 0)    ==: "a 0"

  -- showAlpha for empty and int
  0    =@ "0"
  a 0  =@ "a 0"
  1    =@ "1"
  -1   =@ "-1"
  [0]  =@ "1"
  -[0] =@ "-1"
  a -[0]      =@ "a -1"
  a [a 0,a 0] =@ "a -2"
  a [0,0]     =@ "a 2"
  -- showAlpha for poly
  [1]   =@ "α"
  [1,1] =@ "2α"
  [2]   =: α*α
  [2]   =: α^2
  [a 2] =@ "-α²"
  a [2] =@ "a α²" -- ?
  [a 1]         =@ "-α"
  [0,a 1]       =@ "1-α"
  [a 2,a 2,a 2] =@ "-3α²"
  -[2,2,2]      =@ "-3α²"
  [a 1,a 2]     =@ "-α-α²"
  [a 1,a 1]     =@ "-2α"
  [a 1,2]       =@ "-α+α²"
  [a 1,a 1,2]   =@ "-2α+α²"
  [a 1,a 1,2,2] =@ "-2α+2α²"
  [a 1,a 1,a 2,a 2] =@ "-2α-2α²"
  -- showAlpha for poly (negative exponent)
  [-1] =@ "α⁻¹"
  [-2] =@ "α⁻²"
  [a -1] =@ "-α⁻¹"
  [a -2] =@ "-α⁻²"
  a [a -2] =@ "a -α⁻²"
  a [a -2, 0] =@ "a (-α⁻²+1)"
  -- showAlpha for multi
  [[1],[2],[2],[3]] =@ "α₁+2α₂+α₃"
  [0,[7,2],0] =@ "2+α₂α₇"
  []       =@ "0"
  a []     =@ "a 0"
  [0,a 0]  =@ "0"
  [0]      =@ "1"
  -[0]     =@ "-1"
  [0,0]    =@ "2"
  -[0,0]   =@ "-2"
  [0,a 0,1] =@ "α"
  -- TODO: showAlpha for multi with more anti/negative elements
  [[0]]    =@ "α"  -- we can't tell if this should be α₀ or α, so we use α
  [[1]]    =@ "α₁"
  [[2]]    =@ "α₂"
  -- [[a 1]]  =@ "α₁⁻¹"  -- TODO: fix formatting for Multi
  -- [[a 2]]  =@ "α₂⁻¹"
  -- [[  -1]]  =@ "-α₁"
  -- [[a -1]]  =@ "-α₁⁻¹"

  -- Fractional
  recip α =: [-1]
  recip α =@ "α⁻¹"
  α ^   2 =: [2]  -- ^  is for positive integer exponents only
  α ^^ -1 =: [-1] -- ^^ works with negative integer exponenents too
  α  * (1 / α)  =: 1
  α  * recip α  =: 1
  α₁ * recip α₁ =: 1
  α₂ * recip α₂ =: 1
  -- (2*α)  * recip (2*α)  =: 1  -- TODO: recip isn't applied to 2 because we don't have fractional integers yet
  (α₂^3) * recip (α₂^3) =: 1
  recip α₁ =: [-[1]]
  recip α₁ =: [[a 1]]
  1 / α₁   =: [[a 1]]

  test_MF228
  test_MF232

-- MF228 The big step from polynumbers to multinumbers!!
-- https://www.youtube.com/watch?v=CScJqApRPZg
test_MF228 = do
  -- MF228/1
  0  =: []
  1  =: [0]
  2  =: [0,0]
  3  =: [0,0,0]
  α  =: [1]
  α₀ =: [1]
  -- let m = [[3,3,5],[1],[1],[27,44]]
  -- MF228/4
  2*α₀  =: α₀+α₀
  2*α₀  =: [1,1]
  3*α₀  =: [1,1,1]
  α₀^2  =: α₀*α₀
  α₀^2  =: [2]
  α₀^3  =: [3]
  let p =  [0,0,0,1,3,4,4]
  p     =@ "3+α+α³+2α⁴"  -- for poly we just write α instead of α₀
  α₁    =: [α₀]
  α₁    =: [[1]]
  α₁    =: [[[0]]]
  α₁    =: [[[[]]]]
  -- MF228/5
  2*α₁ =: [α₀, α₀]
  2*α₁ =: [[1],[1]]
  3*α₁ =: [[1],[1],[1]]
  α₁^2 =: α₁*α₁
  α₁^2 =: [α₀+α₀]
  α₁^2 =: [[1,1]]
  α₁^3 =: [[1,1,1]]
  3+α₁+4*α₁^2+α₁^5 =: [0,0,0,[1],[1,1],[1,1],[1,1],[1,1],[1,1,1,1,1]]
  3+α₀+4*α₀^2+α₀^5 =: [0,0,0,1,2,2,2,2,5]
  -- MF228/6
  α₂    =: [[2]]
  α₃    =: [[3]]
  2*α₂  =: [[2],[2]]
  2*α₃  =: [[3],[3]]
  3*α₂  =: [[2],[2],[2]]
  3*α₃  =: [[3],[3],[3]]
  α₁+3*α₂+α₃ =: [[1],[2],[2],[2],[3]]
  α₁^2  =: [[1,1]]
  α₁^3  =: [[1,1,1]]
  α₂^2  =: [[2,2]]
  α₂^3  =: [[2,2,2]]
  α₁*α₂ =: [[1,2]]
  -- MF228/7
  α₀*α₁^2+α₂^3*α₄+2*α₅^3 =: [[0,1,1],[2,2,2,4],[5,5,5],[5,5,5]]
  [[1,5],[0,3,3]] * [2,[1,1,1]] =@ "α₀³α₃²+α₀α₁³α₃²+α₀²α₁α₅+α₁⁴α₅"  -- ordered slightly differently

-- MF232 More arithmetic with negative msets
-- https://www.youtube.com/watch?v=5Rr-ZT6A7cw
test_MF232 = do
  -- MF232/5
  let p =  [0,0,2,2,2,5]
  p     =@ "2+3α²+α⁵"
  -p    =: [a 0,a 0,a 2,a 2,a 2,a 5]
  -p    =@ "-2-3α²-α⁵"
  let q =  [0,a 1,a 2,3]
  q     =@ "1-α-α²+α³"  -- last term incorrect on the whiteboard in the video
  p + q =: [0,0,0,a 1,2,2,3,5]
  p + q =@ "3-α+2α²+α³+α⁵"
  -- MF232/6
  let r =  (2+α₀) * (3-α₀*α₀)
  r     =: [0,0,0,a 2,0,0,0,a 2,1,1,1,a 3]
  r     =@ "6+3α-2α²-α³"
  let s =  (1-α₀)^3
  s     =: [0,a 1,a 1,a 1,2,2,2,a 3]
  s     =@ "1-3α+3α²-α³"
  -- MF232/7
  let t =  [-2,-1,-1,-1,0,3,3]
  t =: t
  t     =@ "α⁻²+3α⁻¹+1+2α³" --
  -- MF232/8
  let u =  [-1,-1,2] + [-3,1,2,4]
  u     =: [-1,-1,-3,1,2,2,4]
  u     =@ "α⁻³+2α⁻¹+α+2α²+α⁴"
  let v =  [-3,-1,a 2] + [a -1,0,2,3]
  v     =: [-3,0,3]
  v     =@ "α⁻³+1+α³"
  let w =  [-2,1] * [-1,-1,a 3]
  w     =: [-3,-3,a 1,0,0, a 4]
  w     =@ "2α⁻³+2-α-α⁴"
