#!/bin/bash

coqc coq/Test.v
coqc coq/Lift.v

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
coqc main.v
cd ..
