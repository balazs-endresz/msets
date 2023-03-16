Haskell implementation of msets, based on the following videos:

* [The big step from polynumbers to multinumbers!! | Math Foundations 228 | N J Wildberger](https://www.youtube.com/watch?v=CScJqApRPZg)
* [The operation of caret / exponentiation (new!) via multisets | Math Foundations 229 | N J Wildberger](https://www.youtube.com/watch?v=TqKacqHS-fA)
* [Multiset arithmetic via trees | Math Foundations 230 | N J Wildberger](https://www.youtube.com/watch?v=62mY0kRQgsg)
* [Negatives numbers from anti msets | Math Foundations 231 | N J Wildberger](https://www.youtube.com/watch?v=KQ1o_NYhQNA)
* [More arithmetic with negative msets | Math Foundations 232 | N J Wildberger](https://www.youtube.com/watch?v=5Rr-ZT6A7cw)

TODO:

* [ ] Fix `showAlpha` for polynumbers and handle an anti-mset of anti-msets correctly.

Click the button below to start a new development environment:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/balazs-endresz/msets)

(There might be some errors initially but those should clear after a minute as it installs everything.)

Then type `ghci` in the terminal in the bottom panel. Within `ghci` one can perform operations with msest:

```hs
ghci> -0        -- anti-zero is represented as -0
-0
ghci> -[]       -- anti-msets are also using the same prefix operator (without a space)
-0
ghci> [1] + -0  -- adding -0 creates an anti mset
-[1]
ghci> [1] - 0   -- negation currently works more like with ordinary integers,
[1]             -- but this might change later, see the `neg` function in `src/Msets.hs`
ghci> [1,[2]] * [[3]]
[[0,3],[2,3]]
ghci> showAlpha [0,1,[2,3,3]]   -- render msets as expressions using alpha
1+α₀+α₂α₃²                      -- (the logic of this will change for anti/negative values!)
ghci> [1] + -0 == -[1]       -- type error, try adding a type annotation:
ghci> [1] + -0 == (-[1]::M)  -- the type M is applied to one of the sub-expressions
True
ghci> [1] + -0 == fix -[1]   -- the `fix` function does the same
True
```

Most of the source code is in `src/Msets.hs`.

Note that by the default `ghci` will use `RebindableSyntax`, but `src/Msets.hs` is currently written without it.

The project is based on https://github.com/lsmor/template-haskell and bumps the default ghc version to 9.4.4

To run locally install https://www.haskell.org/ghcup/ Upgrading the default ghc version might be needed too: `ghcup set ghc 9.4.4`. Then just type `ghci`.
