#!/bin/sh
set -e
pushd /tmp
  git clone https://github.com/imeckler/cabalparse.git
  pushd cabalparse
    cabal sandbox init
    cabal configure
    cabal install
    mv .cabal-sandbox/bin/cabalparse /usr/local/bin
  popd
  rm -rf cabalparse

  git clone https://github.com/imeckler/auto.git
  pushd auto
    cabal sandbox init
    cabal configure
    cabal install
    mv .cabal-sandbox/bin/slick /usr/local/bin
    if [ -d "~/.vim/bundle" ]; then
      mv vim ~/.vim/bundle/slick-vim
    fi
  popd
  rm -rf auto
popd

