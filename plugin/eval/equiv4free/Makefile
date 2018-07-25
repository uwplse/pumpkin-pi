main.vo: main.v lemmas.vo perm.vo list.vo
	coqc main.v

lemmas.vo: lemmas.v perm.vo list.vo
	coqc lemmas.v

perm.vo: perm.v list.vo
	coqc perm.v

list.vo: list.v
	coqc list.v
