#!/bin/bash

coqc coq/Test.v
coqc coq/Lift.v
cd eval
coqc main.v
cd ..
