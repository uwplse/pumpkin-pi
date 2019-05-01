#!/bin/bash

# This runs the first of two versions of the eval, which uses separate datatypes.
# This essentially shows that the performance is still fast even if we lift the datatypes ourselves.

# This is not the version of the eval in the paper, which uses the same datatypes for both and copies and pastes the function,
# to control for changes in performance between regular Coq and Coq with EFF. This version produces times for both
# the EFF base version and the vanilla base version.

if [ -e out ]
then
  rm -r out
else
  :
fi

if [ -e separateequiv ]
then
  rm -r separateequiv
else
  :
fi

if [ -e equiv4free/mainequiv2.v ]
then
  rm equiv4free/mainequiv2.v
else
  :
fi

mkdir out
mkdir out/inorder
mkdir out/postorder
mkdir out/preorder
mkdir out/search
mkdir out/equivalences
mkdir out/normalized
mkdir separateequiv
mkdir separateequiv/inorder
mkdir separateequiv/postorder
mkdir separateequiv/preorder
mkdir separateequiv/search
cp equiv4free/mainequiv.v equiv4free/mainequiv2.v

# Run ten iterations of comparison
for i in {1..10}
do
  echo "Run #${i}"

  # Remake DEVOID case study code
  make clean
  make

  # Copy the produced equivalences into the EFF code
  for f in $(find out/equivalences/*.out); do
    name=$(basename "${f%.*}")
    line=$(grep -n "     : forall" $f | cut -d : -f 1)
    head -n $(($line-1)) $f > out/equivalences/$name-notyp.out
    dirname=$(echo $name | cut -d '-' -f 1)
    suffix=$(echo $name | cut -d '-' -f 2)
    defname=$dirname
    sed -i "s/$defname =/Definition $defname :=/" out/equivalences/$name-notyp.out
    echo "." >> out/equivalences/$name-notyp.out
    term=$(cat out/equivalences/$name-notyp.out)

    # https://stackoverflow.com/questions/29613304/is-it-possible-to-escape-regex-metacharacters-reliably-with-sed
    IFS= read -d '' -r < <(sed -e ':a' -e '$!{N;ba' -e '}' -e 's/[&/\]/\\&/g; s/\n/\\&/g' <<<"$term")
    term=${REPLY%$'\n'}
  
    sed -i "s/(\* EQUIV $name \*)/$term/" equiv4free/mainequiv2.v
  done

  # Remake Univalent Parametricity case study code
  cd equiv4free
  make clean
  make equiv
  cd ..

  # Add the computation times to the aggregate files
  for f in $(find out/*/*.out); do
    name=$(basename "${f%.*}")
    dirname=$(dirname "${f%.*}" | cut -d / -f 2)
    if [ $dirname == "normalized" ]
    then
      :
    else
      tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> separateequiv/$dirname/$name.out
    fi
  done
done

# Add the distribution data
for f in $(find separateequiv/*/*.out); do
  name=$(dirname "${f%.*}" | cut -d / -f 2)"-"$(basename "${f%.*}")
  data=$(datamash median 1 < $f)
  echo "$name : $data" >> separateequiv/medians.out
done

# Measure normalized term size
for f in $(find out/normalized/*.out); do
  name=$(basename "${f%.*}")
  line=$(grep -n "     : forall" $f | cut -d : -f 1)
  head -n $(($line-1)) $f > out/normalized/$name-notyp.out
  loc=$(coqwc -s out/normalized/$name-notyp.out)
  echo $loc >> separateequiv/sizes.out
done
sed -i "s/out\/normalized\///" separateequiv/sizes.out
sed -i "s/-notyp.out//" separateequiv/sizes.out

# Clean temporary files
rm -r out


