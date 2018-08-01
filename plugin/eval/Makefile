main.vo: main.v lemmas.vo cast.vo
	coqc main.v

lemmas.vo: lemmas.v
	coqc lemmas.v

cast.vo: cast.v
	coqc cast.v

clean:
	rm -f *.vo *.glob
