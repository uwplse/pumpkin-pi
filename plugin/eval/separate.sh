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
mkdir out/normalized
mkdir separate
mkdir separate/inorder
mkdir separate/postorder
mkdir separate/preorder
mkdir separate/search

for i in {1..10}
do
  echo "Run #${i}"

  # Remake DEVOID case study code
  make clean
  make

  # Remake Univalent Parametricity case study code
  cd equiv4free
  make clean
  make
  cd ..

  # Add the computation times to the aggregate files
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
done

# Add the distribution data
for f in $(find separate/*/*.out); do
  name=$(basename "${f%.*}")
  data=$(datamash median 1 < $f)
  echo "$name : $data" >> separate/medians.out
  echo $'\n' >> separate/medians.out
done

# Measure normalized term size
for f in $(find out/normalized/*.out); do
  name=$(basename "${f%.*}")
  line=$(grep -n "     : forall" $f | cut -d : -f 1)
  head -n $(($line-1)) $f > out/normalized/$name-notyp.out
  loc=$(coqwc -s out/normalized/$name-notyp.out)
  echo $loc >> separate/sizes.out
done
sed -i "s/out\/normalized\///" separate/sizes.out
sed -i "s/-notyp.out//" separate/sizes.out

# Clean temporary files
rm -r out


