# Mote

The programmer's assistant. Discharge your burdens with style.

Mote brings the development style found in Agda to Haskell, currently only
as a vim plugin.

# Requirements
  Mote uses [pathogen](https://github.com/tpope/vim-pathogen) for the vim plugin and
  assumes you install pathogen bundles to `~/.vim/bundle`.

# Installation
Pick one of the following. 

1. If you trust me and are okay with programs being installed to `/usr/local/bin`,
   just do
   ```bash
   curl https://raw.githubusercontent.com/imeckler/mote/master/scripts/install.sh | bash
   ```

   Mote does not set any key bindings for the commands it provides, but a suggested set
   is given (commented out) [here](/vim/ftplugin/haskell.vim).

2. If you don't or aren't, do what the script does:
  - First install [cabalparse](https://github.com/imeckler/cabalparse) and
    make sure it's on your path.
  - Install `mote` via cabal install:

    ```bash
    git clone https://github.com/imeckler/mote.git
    cd mote
    cabal sandbox init
    cabal install mote -j
    mv .cabal-sandbox/bin/mote ~/.cabal/bin # or wherever
    ```
  - Install the vim plugin (which is in the `vim` directory of the repo)

3. Personally, I would do this since it makes updating easy. First install
   [cabalparse](https://github.com/imeckler/cabalparse) and then
  ```bash
  mkdir ~/sandboxes # or wherever
  cd sandboxes
  git clone https://github.com/imeckler/mote.git
  cd mote
  cabal sandbox init
  cabal install mote -j
  ```
  and then symlink `~/sandboxes/mote/.cabal-sandbox/bin/mote` to somewhere
  on your path. That way, updating is as easy as going to
  `sandboxes/mote`, doing a `git pull` followed by `cabal install` without
  having to reinstall dependencies.
  
# Documentation

Mote provides the following vim commands.

- `MoteLoadCurrentFile`

  (Re)loads the current file. By default, this is called on every file write.
  The first load takes a few seconds, but things should be snappy after that.

- `MoteToggleMode`

  Toggles whether `MoteLoadCurrentFile` gets called on every write.

- `MoteNextHole`

  Jumps the cursor to the next hole and displays bindings in scope in the hole as
  well as the goal type. I recommend binding this to `option+k`.

- `MotePrevHole`

  Jumps the cursor to the previous hole and displays bindings in scope in the hole as
  well as the goal type. I recommend binding this to `option+j`.

- `Casex`

  If `x` is a variable bound in a pattern match whose right hand side contains the
  current hole, `:Casex x` expands the pattern to case further on `x`. For example,
  if we have
  ```haskell
  f :: [a] -> Int
  f xs = _
  ```
  then typing `:Casex xs` results in
  ```haskell
  f :: [a] -> Int
  f []     = _
  f (x:xs) = _
  ```

- `CaseOn`

  Fills the current hole by casing on some expression. For example, if we have
  ```haskell
  f :: [a] -> Int
  f xs = _
  ```
  then typing `:CaseOn xs` results in
  ```haskell
  f :: [a] -> Int
  f xs = case xs of
    []      -> _
    x : xs' -> _
  ```

- `MoteRefine`

  Partially fill the current hole by providing a function that maps into the
  goal type. For example, if we have
  ```haskell
  f :: [a] -> Int
  f xs = _
  ```
  then typing `:MoteRefine length` will result in
  ```haskell
  f :: [a] -> Int
  f xs = length _
  ```
  I recommend binding this to `option+r`.

- `MoteStart`

  Starts a Mote process running in the background. This is called automatically
  when a Haskell file is loaded and you should never need to call it.

# Example session
When you don't know how to complete a program, you type a `_` as a placeholder.
For example, if we're writing a `map` function, we would put an underscore `_`
on the right hand side initially. We'll call our function `map'` so as not to
clash with the Prelude function.

![](/images/readme/1.png)
We then start the editing session by calling `:MoteLoadCurrentFIle`

An underscore expression is called a *hole*. When programming with Mote, there is
a notion of the "current hole": the unfinished expression currently being worked on.

When you want to work on a particular hole, you *enter* the hole. The command in the
Mote vim plugin is `:call mote#nextHole()`, which jumps your cursor to the next
hole.
![](/images/readme/3.png)

You'll notice that there is now an `@` in the leftmost column, indicating the line
of the current hole, and a new window has popped up displaying some information.

The information displayed is the "goal type", the type inferred for the current hole,
and the names and types of local variables, which are likely to be useful for filling
the hole. (In the future, this window will also display non-local values which are
likely to be useful based on the hole type).

We now decide to pattern match on `xs`, and so we type `:Casex xs`, which expands a variable
bound in a pattern
![](/images/readme/4.png)
and we jump to the next hole after filling it with `_ : _`.
![](/images/readme/5.png)

Since our goal type is `b`, and we have a function `f` that returns a value of type `b`,
we can *refine* the hole with `f`.
![](/images/readme/6.png)
by typing `:MoteRefine f`.

In general, if you are in a hole of type `T`, you can refine with an arbitrary expression
of type `A1 -> ... -> An -> T`, which may itself contain holes.

We can then blow through the rest of the definition, alternatingly
calling `mote#nextHole()` and `MoteRefine` to finally get
![](/images/readme/10.png)

