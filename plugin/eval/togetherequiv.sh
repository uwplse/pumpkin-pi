#!/bin/bash

# This runs the second of two versions of the eval, which is the version of the eval in the paper; 
# it uses the same datatypes for both and copies and pastes the function,
# to control for changes in performance between regular Coq and Coq with EFF.

if [ -e out ]
then
  rm -r out
else
  :
fi

if [ -e togetherequiv ]
then
  rm -r togetherequiv
else
  :
fi

if [ -e main2.v ]
then
  rm main2.v
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
mkdir togetherequiv
mkdir togetherequiv/inorder
mkdir togetherequiv/postorder
mkdir togetherequiv/preorder
mkdir togetherequiv/search
cp main.v main2.v
cp equiv4free/main.v equiv4free/main2.v
cp equiv4free/mainequiv.v equiv4free/mainequiv2.v

# Set DEVOID case study code to print regular terms instead of computed ones
sed -i "s/Eval compute in/Print/" main2.v

# Remake DEVOID case study code exactly once, to print terms
make clean
make together

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

# Copy the produced terms into the EFF code, to run everything together
for f in $(find out/normalized/*.out); do
  name=$(basename "${f%.*}")
  line=$(grep -n "     : forall" $f | cut -d : -f 1)
  head -n $(($line-1)) $f > out/normalized/$name-notyp.out
  dirname=$(echo $name | cut -d '-' -f 1)
  suffix=$(echo $name | cut -d '-' -f 2)
  defname=$dirname"'"
  sed -i "s/$defname =/Definition $defname :=/" out/normalized/$name-notyp.out
  echo "." >> out/normalized/$name-notyp.out
  term=$(cat out/normalized/$name-notyp.out)

  # https://stackoverflow.com/questions/29613304/is-it-possible-to-escape-regex-metacharacters-reliably-with-sed
  IFS= read -d '' -r < <(sed -e ':a' -e '$!{N;ba' -e '}' -e 's/[&/\]/\\&/g; s/\n/\\&/g' <<<"$term")
  term=${REPLY%$'\n'}
  
  sed -i "s/(\* DEF $name \*)/$term/" equiv4free/mainequiv2.v
  sed -i "s/(\* NORMALIZE $name \*)/Redirect \"..\/out\/normalized\/$name\" Eval compute in $defname./" equiv4free/mainequiv2.v
 
  sed -i "s/(\* TIME-SEARCH $name \*)/Redirect \"..\/out\/$dirname\/${suffix}1\" Time Eval vm_compute in ($defname _ _ _ _ tree1 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}10\" Time Eval vm_compute in ($defname _ _ _ _ tree10 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}100\" Time Eval vm_compute in ($defname _ _ _ _ tree100 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}1000\" Time Eval vm_compute in ($defname _ _ _ _ tree1000 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}10000\" Time Eval vm_compute in ($defname _ _ _ _ tree10000 Elem.x)./" equiv4free/mainequiv2.v
  
  sed -i "s/(\* TIME-AVL $name \*)/Redirect \"..\/out\/$dirname\/${suffix}1\" Time Eval vm_compute in ($defname _ _ _ _ tree1).\n\tRedirect \"..\/out\/$dirname\/${suffix}10\" Time Eval vm_compute in ($defname _ _ _ _ tree10).\n\tRedirect \"..\/out\/$dirname\/${suffix}100\" Time Eval vm_compute in ($defname _ _ _ _ tree100).\n\tRedirect \"..\/out\/$dirname\/${suffix}1000\" Time Eval vm_compute in ($defname _ _ _ _ tree1000).\n\tRedirect \"..\/out\/$dirname\/${suffix}10000\" Time Eval vm_compute in ($defname _ _ _ _ tree10000)./" equiv4free/mainequiv2.v
  
  sed -i "s/(\* TIME-SIZED $name \*)/Redirect \"..\/out\/$dirname\/${suffix}1\" Time Eval vm_compute in ($defname tree1).\n\tRedirect \"..\/out\/$dirname\/${suffix}10\" Time Eval vm_compute in ($defname tree10).\n\tRedirect \"..\/out\/$dirname\/${suffix}100\" Time Eval vm_compute in ($defname tree100).\n\tRedirect \"..\/out\/$dirname\/${suffix}1000\" Time Eval vm_compute in ($defname tree1000).\n\tRedirect \"..\/out\/$dirname\/${suffix}10000\" Time Eval vm_compute in ($defname tree10000)./" equiv4free/mainequiv2.v
done

# Clean outputted directories
rm -r out
mkdir out
mkdir out/inorder
mkdir out/postorder
mkdir out/preorder
mkdir out/search
mkdir out/normalized

# Run ten iterations of comparison
for i in {1..10}
do
  echo "Run #${i}"

  # Remake Univalent Parametricity case study code
  cd equiv4free
  make clean
  make equiv
  cd ..

  # Add the computation times to the aggregate files
  for f in $(find out/*/*.out); do
    name=$(basename "${f%.*}")
    dirname=$(dirname "${f%.*}" | cut -d / -f 2)
    if [ $dirname == "normalized" ] || [ $dirname == "equivalences" ]
    then
      :
    else
      tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> togetherequiv/$dirname/$name.out
    fi
  done
done

# Add the distribution data
for f in $(find togetherequiv/*/*.out); do
  name=$(dirname "${f%.*}" | cut -d / -f 2)"-"$(basename "${f%.*}")
  data=$(datamash median 1 < $f)
  echo "$name : $data" >> togetherequiv/medians.out
done

# Measure normalized term size
for f in $(find out/normalized/*.out); do
  name=$(basename "${f%.*}")
  line=$(grep -n "     : forall" $f | cut -d : -f 1)
  head -n $(($line-1)) $f > out/normalized/$name-notyp.out
  loc=$(coqwc -s out/normalized/$name-notyp.out)
  echo $loc >> togetherequiv/sizes.out
done

# Format term size data
sed -i "s/out\/normalized\///" togetherequiv/sizes.out
sed -i "s/-notyp.out//" togetherequiv/sizes.out

# Preprocess for sanity checks
rm -r out/normalized
for f in $(find out/*/*.out); do
  tail -n 2 $f > $f
done

# Run sanity checks
for f in $(find out/*/*EFF*.out); do
  name=$(basename "${f%.*}")
  if [[ $name =~ ^base.* ]]
  then
    :
  else
    g=$(echo $f | sed -e "s/EFFequiv//")
    echo "Sanity checking $f and $g."
    if [ "$(cat $f)" == "$(cat $g)" ]
    then
      :
    else
      echo "Sanity check failed. $f and $g are different." 1>&2
      exit 1
    fi
  fi
done

# Clean temporary files
rm -r out
rm main2.v
rm equiv4free/main2.v # You can comment out this line if you want to see the output file with everything together

