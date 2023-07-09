Haskell implementation of msets, based on the following videos:

* [The big step from polynumbers to multinumbers!! | Math Foundations 228 | N J Wildberger](https://www.youtube.com/watch?v=CScJqApRPZg)
* [The operation of caret / exponentiation (new!) via multisets | Math Foundations 229 | N J Wildberger](https://www.youtube.com/watch?v=TqKacqHS-fA)
* [Multiset arithmetic via trees | Math Foundations 230 | N J Wildberger](https://www.youtube.com/watch?v=62mY0kRQgsg)
* [Negatives numbers from anti msets | Math Foundations 231 | N J Wildberger](https://www.youtube.com/watch?v=KQ1o_NYhQNA)
* [More arithmetic with negative msets | Math Foundations 232 | N J Wildberger](https://www.youtube.com/watch?v=5Rr-ZT6A7cw)

Click the button below to start a new development environment:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/balazs-endresz/msets)

(There might be some errors initially but those should clear after a minute as it installs everything.)

Then type `ghci` in the terminal in the bottom panel. Within `ghci` one can perform operations with msest:

```hs
ghci> :t 1
1 :: Mset (Mset a)  -- numeric literals should be msets by default in ghci, see the `.ghci` file
ghci> [1] + a 0 -- adding anti zero creates an anti mset
a [1]
ghci> -[0,0]    -- make the elements "anti"
-2              -- == [-0,-0]
ghci> a -[0,0]  -- the function `a` makes an mset an anti-mset (not the elements)
a -2            -- == a [-0,-0]
ghci> [1,[2]] * [[3]]
[[0,3],[2,3]]
ghci> showAlpha' [-1,-1,-3,1,2,2,4]  -- showAlpha' is a shortcut for `showAlpha ([...]::M)`
α⁻³+2α⁻¹+α+2α²+α⁴
ghci> [1] + a 0 == a [1]       -- type error, try adding a type annotation:
ghci> [1] + a 0 == (a [1]::M)  -- the type M is applied to one of the sub-expressions
True
ghci> [1] + a 0 == fix (a [1]) -- the `fix` function does the same
True
```

Most of the source code is in `src/Msets.hs`.

Note that by the default `ghci` will use `RebindableSyntax`, but `src/Msets.hs` is currently written without it.

The project is based on https://github.com/lsmor/template-haskell and bumps the default ghc version to 9.4.4

To run locally install https://www.haskell.org/ghcup/ Upgrading the default ghc version might be needed too: `ghcup set ghc 9.4.4`. Then just type `ghci`.
