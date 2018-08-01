#!/bin/bash

# This runs the first of two versions of the eval, which uses separate datatypes.
# This essentially shows that the performance is still fast even if we lift the datatypes ourselves.

# This is not the version of the eval in the paper, which uses the same datatypes for both and copies and pastes the function,
# to control for changes in performance between regular Coq and Coq with UP. This version produces times for both
# the UP base version and the vanilla base version.

if [ -e out ]
then
  rm -r out
else
  :
fi

if [ -e separate ]
then
  rm -r separate
else
  :
fi

mkdir out
mkdir out/inorder
mkdir out/postorder
mkdir out/preorder
mkdir out/search
mkdir separate
mkdir separate/inorder
mkdir separate/postorder
mkdir separate/preorder
mkdir separate/search

for i in {1..10}
do
  make clean
  make

  cd equiv4free
  make clean
  make

  cd ..

  for f in $(find out/preorder/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> separate/preorder/$name.out
  done

  for f in $(find out/postorder/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> separate/postorder/$name.out
  done

  for f in $(find out/inorder/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> separate/inorder/$name.out
  done

  for f in $(find out/search/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> separate/search/$name.out
  done

  # TODO run the other code too
  # TODO version w/ same datatypes
  # TODO automatically take medians
done

# clean temporary files
rm -r out


