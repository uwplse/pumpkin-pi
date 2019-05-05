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

echo "grab a coffee or a book; this will take an hour on the right architecture once you've uncommented the right line"
timeout 1h `time make separate`

# Measure normalized term size
for f in $(find ../out/normalized/pre_permutes-sizedEFF.out); do
  name=$(basename "${f%.*}")
  line=$(grep -n "     : forall" $f | cut -d : -f 1)
  head -n $(($line-1)) $f > ../out/normalized/$name-notyp.out
  coqwc -s ../out/normalized/$name-notyp.out
done
