#!/bin/bash
set -e

install_cabalparse() {
  if [ -d cabalparse ]; then
    rm -rf cabalparse
  fi
  git clone https://github.com/imeckler/cabalparse.git
  pushd cabalparse
    cabal sandbox init
    cabal install -j
    sudo mv .cabal-sandbox/bin/cabalparse /usr/local/bin
  popd
  rm -rf cabalparse
}

pushd /tmp
  which cabalparse || install_cabalparse

  if [ -d mote ]; then
    rm -rf mote
  fi
  git clone https://github.com/imeckler/mote.git
  pushd mote
    cabal sandbox init
    cabal install -j
    sudo mv .cabal-sandbox/bin/mote /usr/local/bin
    if [ -d "~/.vim/bundle" ]; then
      mv vim ~/.vim/bundle/vim-mote
    fi
  popd
  rm -rf mote
popd

