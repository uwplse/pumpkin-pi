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

if [ -e together ]
then
  rm -r together
else
  :
fi

if [ -e main2.v ]
then
  rm main2.v
else
  :
fi

mkdir out
mkdir out/inorder
mkdir out/postorder
mkdir out/preorder
mkdir out/search
mkdir out/normalized
mkdir together
mkdir together/inorder
mkdir together/postorder
mkdir together/preorder
mkdir together/search
cp main.v main2.v
cp equiv4free/main.v equiv4free/main2.v

# Set DEVOID case study code to print regular terms instead of computed ones
sed -i "s/Eval compute in/Print/" main2.v

# Remake DEVOID case study code exactly once, to print terms
make clean
make together

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
  
  sed -i "s/(\* DEF $name \*)/$term/" equiv4free/main2.v
  sed -i "s/(\* NORMALIZE $name \*)/Redirect \"..\/out\/normalized\/$name\" Eval compute in $defname./" equiv4free/main2.v
 
  if [ $defname == "search'" ]
  then 
     sed -i "s/(\* TIME-SMALL $name \*)/Redirect \"..\/out\/$dirname\/${suffix}20\" Time Eval vm_compute in ($defname _ _ _ _ tree20.2 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}40\" Time Eval vm_compute in ($defname _ _ _ _ tree40.2 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}60\" Time Eval vm_compute in ($defname _ _ _ _ tree60.2 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}80\" Time Eval vm_compute in ($defname _ _ _ _ tree80.2 Elem.x).\n\tRedirect \"..\/out\/$dirname\/${suffix}100\" Time Eval vm_compute in ($defname _ _ _ _ tree100.2 Elem.x)./" equiv4free/main2.v
  else
    sed -i "s/(\* TIME-SMALL $name \*)/Redirect \"..\/out\/$dirname\/${suffix}20\" Time Eval vm_compute in ($defname _ _ _ _ tree20.2).\n\tRedirect \"..\/out\/$dirname\/${suffix}40\" Time Eval vm_compute in ($defname _ _ _ _ tree40.2).\n\tRedirect \"..\/out\/$dirname\/${suffix}60\" Time Eval vm_compute in ($defname _ _ _ _ tree60.2).\n\tRedirect \"..\/out\/$dirname\/${suffix}80\" Time Eval vm_compute in ($defname _ _ _ _ tree80.2).\n\tRedirect \"..\/out\/$dirname\/${suffix}100\" Time Eval vm_compute in ($defname _ _ _ _ tree100.2)./" equiv4free/main2.v
    sed -i "s/(\* TIME-BIG $name \*)/Redirect \"..\/out\/$dirname\/${suffix}2000\" Time Eval vm_compute in ($defname tree2000).\n\tRedirect \"..\/out\/$dirname\/${suffix}4000\" Time Eval vm_compute in ($defname tree4000).\n\tRedirect \"..\/out\/$dirname\/${suffix}6000\" Time Eval vm_compute in ($defname tree6000).\n\tRedirect \"..\/out\/$dirname\/${suffix}8000\" Time Eval vm_compute in ($defname tree8000).\n\tRedirect \"..\/out\/$dirname\/${suffix}10000\" Time Eval vm_compute in ($defname tree10000)./" equiv4free/main2.v
  fi
done

# Clean outputted directories
rm -r out
mkdir out
mkdir out/inorder
mkdir out/postorder
mkdir out/preorder
mkdir out/search
mkdir out/normalized

for i in {1..10}
do
  echo "Run #${i}"

  # Remake Univalent Parametricity case study code
  cd equiv4free
  make clean
  make together
  cd ..

  # Add the computation times to the aggregate files
  for f in $(find out/preorder/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> together/preorder/$name.out
  done

  for f in $(find out/postorder/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> together/postorder/$name.out
  done

  for f in $(find out/inorder/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> together/inorder/$name.out
  done

  for f in $(find out/search/*.out); do
    name=$(basename "${f%.*}")
    tail -n 2 $f | grep -o -e '[0-9.]* secs' | sed -f times.sed >> together/search/$name.out
  done
done

# Add the distribution data
for f in $(find together/*/*.out); do
  name=$(basename "${f%.*}")
  data=$(datamash median 1 < $f)
  echo "$name : $data" >> together/medians.out
done

# Measure normalized term size
for f in $(find out/normalized/*.out); do
  name=$(basename "${f%.*}")
  line=$(grep -n "     : forall" $f | cut -d : -f 1)
  head -n $(($line-1)) $f > out/normalized/$name-notyp.out
  loc=$(coqwc -s out/normalized/$name-notyp.out)
  echo $loc >> together/sizes.out
done

sed -i "s/out\/normalized\///" together/sizes.out
sed -i "s/-notyp.out//" together/sizes.out

# Clean temporary files
rm -r out
rm main2.v
rm equiv4free/main2.v # You can uncomment this line if you want to see the output file with everything together

