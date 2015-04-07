#!/bin/bash
set -e
pushd /tmp
  git clone https://github.com/imeckler/cabalparse.git
  pushd cabalparse
    cabal sandbox init
    cabal configure
    cabal install
    mv .cabal-sandbox/bin/cabalparse /usr/local/bin
  popd

  git clone https://github.com/imeckler/auto.git
  pushd auto
    cabal sandbox init
    cabal configure
    cabal install
    mv .cabal-sandbox/bin/slick /usr/local/bin
  popd
popd

