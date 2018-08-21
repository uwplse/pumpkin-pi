#!/bin/bash

lifted=false
liftedind=false
liftedcase=false

if coqc coq/Test.v 
then
  :
else
  echo "ERROR: Searching for ornaments failed"
  exit 1
fi

if coqc coq/Lift.v 
then
  lifted=true
else
  :
fi

if coqc coq/Indtype.v 
then
  liftedind=true
else
  :
fi

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
make clean
if make
then
  liftedcase=true
else
  :
fi
cd ..

if [ $lifted = true ] && [ $liftedind = true ] && [ $liftedcase = true ]
then
  echo "SUCCESS: All tests passed."
elif [ $lifted = true ] && [ $liftedcase = true ]
then
  echo "WARNING: All POPL tests passed, but lifted inductive predicates are broken. See Coq error message."
else
  echo "ERROR: The following tests failed, including POPL tests:"
  if [ !$lifted = true ]
  then
    echo "lifting"
  else
    :
  fi
  if [ !$liftedind = true ]
  then
    echo "lifting inductive predicates"
  else
    :
  fi
  if [ !$liftedcase = true ]
  then
    echo "case study code"
  else
    :
  fi
  echo "See Coq error message."
fi
  
