#!/bin/bash

coqc coq/Test.v
coqc coq/Lift.v
coqc coq/Indtype.v

cd eval

if [ -e out ]
then
  rm -r out
else
  :
fi

mkdir out
mkdir out/inorder
mkdir out/postorder
mkdir out/preorder
mkdir out/search
mkdir out/normalized
make clean && make
cd ..
