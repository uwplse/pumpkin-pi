#!/usr/bin/env bash
git submodule init
git submodule update
echo "making makefile and cleaning"
coq_makefile -f _CoqProject -o Makefile
make clean
echo "building dependencies"
cd deps/fix-to-elim/plugin
./build.sh
cd ../../..
echo "building DEVOID"
make && make install

