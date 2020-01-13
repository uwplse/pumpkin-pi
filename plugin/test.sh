#!/bin/bash

lifted=false
liftedind=false
findlift=false
liftedcase=false
assumptions=false
intro=false
example=false
liftspec=false
search=false
lift=false
listtovect=false
records=false
morerecords=false
smartcache=false
nosmartcache=false
prodrect=false

coqc coq/Infrastructure.v

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

echo "Testing Lift with implicit Find Ornament."

if coqc coq/TestFindLift.v
then
  findlift=true
else
  :
fi

echo "Testing Lift Record."

if coqc coq/minimal_records.v
then
  records=true
else
  :
fi

if coqc coq/more_records.v
then
  morerecords=true
else
  :
fi

cd coq

if coqc prod_rect.v
then
  prodrect=true
else
  :
fi

cd ..

echo "Testing smart cache."
echo "First, without the smart cache:"

if coqc coq/NoSmartCache.v
then
  nosmartcache=true
else
  :
fi

echo "Now, with the smart cache:"

if coqc coq/SmartCache.v
then
  smartcache=true
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
  caseend=$SECONDS # TODO this is not correct
  liftedcase=true
else
  :
fi
cd ..

echo "Running ITP paper examples."

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

if coqc coq/examples/Assumptions.v
then
  assumptions=true
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

if [ $lifted = true ] && [ $liftedind = true ] && [ $findlift = true ] &&    
   [ $liftedcase = true ] && [ $assumptions = true ] && [ $intro = true ] &&
   [ $example = true ] && [ $liftspec = true ] && [ $search = true ] && 
   [ $lift = true ] && [ $listtovect = true ] && [ $records = true ] &&
   [ $morerecords = true ] && [ $nosmartcache = true ] && [ $smartcache = true ] && [ $prodrect = true ]
then
  echo "SUCCESS: All tests passed."

  caseelapsed=($caseend - $casestart) 
  echo "Case study code took $caseelapsed seconds."
else
  echo "ERROR: The following tests failed:"
  if [ $lifted = false ]
  then
    echo "lifting"
  else
    :
  fi
  if [ $findlift = false ]
  then
    echo "lifting with implicit Find Ornament"
  else
    :
  fi
  if [ $liftedind = false ]
  then
    echo "lifting inductive predicates"
  else
    :
  fi
  if [ $records = false ]
  then
    echo "lifting records to products: minimal test"
  else
    :
  fi
  if [ $morerecords = false ]
  then
    echo "lifting records to products: fancier test"
  else
    :
  fi
  if [ $prodrect = false ]
  then
    echo "lifting records to products: folding projections"
  else
    :
  fi
  if [ $smartcache = false ]
  then
    echo "set smart cache test"
  else
    :
  fi
  if [ $nosmartcache = false ]
  then
    echo "unset smart cache test"
  else
    :
  fi
  if [ $liftedcase = false ]
  then
    echo "case study code"
  else
    :
  fi
  if [ $assumptions = false ]
  then
    echo "Assumptions.v from ITP examples"
  else
    :
  fi
  if [ $intro = false ]
  then
    echo "Intro.v from ITP examples"
  else
    :
  fi
  if [ $example = false ]
  then
    echo "Example.v from ITP examples"
  else
    :
  fi
  if [ $liftspec = false ]
  then
    echo "LiftSpec.v from ITP examples"
  else
    :
  fi
  if [ $search = false ]
  then
    echo "Search.v from ITP examples"
  else
    :
  fi
  if [ $lift = false ]
  then
    echo "Lift.v from ITP examples"
  else
    :
  fi
  if [ $listtovect = false ]
  then
    echo "ListToVect.v from ITP examples"
  else
    :
  fi
  echo "See Coq error message."
fi

