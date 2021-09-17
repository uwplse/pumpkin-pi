#!/usr/bin/env bash
git submodule init
git submodule update
echo "building dependencies"
cd deps/fix-to-elim/plugin
./build.sh
cd ../../..
echo "building PUMPKIN Pi"

dune clean
dune build @all
dune install

