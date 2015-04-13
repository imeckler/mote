# slick

The programmer's assistant. Discharge your burdens with style.

Slick brings the development style found in Agda to Haskell, currently only
as a vim plugin. In this section, I'll give an idea of what programming with
the slick vim plugin is like.

When you don't know how to complete a program, you type a `_` as a placeholder.
For example, if we're writing a `map` function, we would put an underscore `_`
on the right hand side initially. We'll call our function `map'` so as not to
clash with the Prelude function.
```haskell
map' :: (a -> b) -> [a] -> [b]
map' f xs = _
```
An underscore expression is called a *hole*. When programming with slick, there is
a notion of the "current hole": the unfinished expression currently being worked on.

When you want to work on a particular hole, you *enter* the hole. The command in the
slick vim plugin is `:call slick#nextHole()`, which jumps your cursor to the next
hole 

# Installation
1. If you trust me and are okay with programs being installed to `/usr/local/bin`,
   just do
   ```bash
   curl https://raw.githubusercontent.com/imeckler/auto/master/scripts/install.sh | bash
   ```

2. If you don't or aren't, do what the script does:
  - First install [cabalparse](https://github.com/imeckler/cabalparse) and
    make sure it's on your path.
  - Install `slick` via cabal install:

    ```bash
    git clone https://github.com/imeckler/auto.git
    cd auto
    cabal sandbox init
    cabal configure
    cabal install
    mv .cabal-sandbox/bin/slick ~/.cabal/bin # or wherever
    ```
