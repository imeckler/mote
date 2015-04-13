# slick

The programmer's assistant. Discharge your burdens with style.

Slick brings the development style found in Agda to Haskell, currently only
as a vim plugin. In this section, I'll give an idea of what programming with
the slick vim plugin is like.

When you don't know how to complete a program, you type a `_` as a placeholder.
For example, if we're writing a `map` function, we would put an underscore `_`
on the right hand side initially. We'll call our function `map'` so as not to
clash with the Prelude function.

![](/images/readme/1.png)
We then start the editing session by calling `:SlickLoadCurrentFIle`

An underscore expression is called a *hole*. When programming with slick, there is
a notion of the "current hole": the unfinished expression currently being worked on.

When you want to work on a particular hole, you *enter* the hole. The command in the
slick vim plugin is `:call slick#nextHole()`, which jumps your cursor to the next
hole.
![](/images/3.png)

You'll notice that there is now an `@` in the leftmost column, indicating the line
of the current hole, and a new window has popped up displaying some information.

The information displayed is the "goal type", the type inferred for the current hole,
and the names and types of local variables, which are likely to be useful for filling
the hole. (In the future, this window will also display non-local values which are
likely to be useful based on the hole type).

We now decide to pattern match on `xs`, and so we type `Casex xs`, which expands a variable
bound in a pattern
![](/images/4.png)
and we jump to the next hole after filling it with `_ : _`.
![](/images/5.png)

Since our goal type is `b`, and we have a function `f` that returns a value of type `b`,
we can *refine* the hole with `f`.
![](/images/6.png)
by typing `:SlickRefine f`.

In general, if you are in a hole of type `T`, you can refine with an arbitrary expression
of type `A1 -> ... -> An -> T`, which may itself contain holes.

We can then blow through the rest of the definition, alternatingly
calling `slick#nextHole()` and `SlickRefine` to finally get
![](/images/10.png)

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
