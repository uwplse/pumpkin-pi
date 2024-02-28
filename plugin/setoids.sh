#!/bin/bash

cd coq/playground

echo "Running integer case study"
if coqc grothendieck_int_equivalence_repair_tool.v
then
  :
else
  echo "ERROR: running integer case study failed"
  exit 1
fi

cd TwoListQueue

echo "Building UIPList"
if coqc UIPList.v
then
  :
else
  echo "ERROR: building UIPList failed"
  exit 1
fi


echo "Running queue case study"

if coqc two_list_queue_equivalence_repair_tool.v 
then
  :
else
  echo "ERROR: running queue case study failed"
  exit 1
fi

