#!/bin/bash

# Once you have uncommented the extremely costly normalization in main.v, this script
# verifies the claim that it timed out in an hour trying to normalize it.
# Go grab a coffee or something.

if [ -e ../out ]
then
  rm -r ../out
else
  :
fi

mkdir ../out
mkdir ../out/inorder
mkdir ../out/postorder
mkdir ../out/preorder
mkdir ../out/search
mkdir ../out/normalized

# Remake Univalent Parametricity case study code
make clean

echo "grab a coffee or a book; this will take an hour once you've uncommented the right line"
timeout 1h `time make`

