#!/bin/bash

lifted=false
liftedind=false
liftedcase=false
assumptions=false
intro=false
example=false
liftspec=false
search=false
lift=false
listtovect=false

echo "Testing Find ornament."

if coqc coq/Test.v
then
  :
else
  echo "ERROR: Searching for ornaments failed"
  exit 1
fi

echo "Testing Lift."

if coqc coq/TestLift.v
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

echo "Running case study code."

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
mkdir out/inputs
mkdir out/equivalences
make clean
ulimit -s 100000
casestart=$SECONDS	
if make
then
  caseend=$SECONDS
  liftedcase=true
else
  :
fi
cd ..

echo "Running ITP paper examples."

if coqc coq/examples/Assumptions.v
then
  assumptions=true
else
  :
fi

if coqc coq/examples/Intro.v
then
  intro=true
else
  :
fi

if coqc coq/examples/Example.v
then
  example=true
else
  :
fi

if coqc coq/examples/LiftSpec.v
then
  liftspec=true
else
  :
fi

if coqc coq/examples/Search.v
then
  search=true
else
  :
fi

if coqc coq/examples/Lift.v
then
  lift=true
else
  :
fi

if coqc coq/examples/ListToVect.v
then
  listtovect=true
else
  :
fi

if [ $lifted = true ] && [ $liftedind = true ] && [ $liftedcase = true ] && 
   [ $assumptions = true ] && [ $intro = true ] && [ $example = true ] &&
   [ $liftspec = true ] && [ $search = true ] && [ $lift = true ] &&
   [ $listtovect = true ]
then
  echo "SUCCESS: All tests passed."

  caseelapsed=($caseend - $casestart) 
  echo "Case study code took $caseelapsed seconds."
else
  echo "ERROR: The following tests failed:"
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
  if [ !$assumptions = true ]
  then
    echo "Assumptions.v from ITP examples"
  else
    :
  fi
  if [ !$intro = true ]
  then
    echo "Intro.v from ITP examples"
  else
    :
  fi
  if [ !$example = true ]
  then
    echo "Example.v from ITP examples"
  else
    :
  fi
  if [ !$liftspec = true ]
  then
    echo "LiftSpec.v from ITP examples"
  else
    :
  fi
  if [ !$search = true ]
  then
    echo "Search.v from ITP examples"
  else
    :
  fi
  if [ !$lift = true ]
  then
    echo "Lift.v from ITP examples"
  else
    :
  fi
  if [ !$listtovect = true ]
  then
    echo "ListToVect.v from ITP examples"
  else
    :
  fi
  echo "See Coq error message."
fi

