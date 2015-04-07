# slick

The programmer's assistant. Discharge your burdens with style.

# Installation
1. If you trust me and are okay with programs being installed to `/usr/local/bin`,
   just do
   ```bash
   curl https://raw.githubusercontent.com/imeckler/auto/master/scripts/install.sh | sh
   ```

2. If you don't, do what the script does:
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
