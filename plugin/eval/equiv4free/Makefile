lemmas.vo: lemmas.v perm.vo list.vo
	coqc lemmas.v

perm.vo: perm.v list.vo
	coqc perm.v

list.vo: list.v
	coqc list.v

clean:
	rm -f *.vo *.glob

equiv: main2.v lemmas.vo perm.vo list.vo
	coqc main2.v

