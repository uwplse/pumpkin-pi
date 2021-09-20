#!/usr/bin/env bash
echo "Make sure you have coq-plugin-lib and fix-to-elim installed first"
echo "Building PUMPKIN Pi"

dune clean
dune build @all
dune build @all # annoying hack for first build loadpath issue
dune install

