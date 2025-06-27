## Quotient Types Extension to Pumpkin Pi
This document describes the quotient types/setoids extension to the existing PUMPKIN Pi infrastructure.
To fetch and build everything, make sure you have Coq 8.9.1 installed (later versions are not currently supported).
Building was tested using both Ubuntu 22.04.5 and 24.04.2, but other Unix based systems may also work, as well as the Windows Subsystem for Linux.

Then, to build everything, run:
```
cd plugin
bash build.sh
```

To run the relevant case studies files, run:
```
bash setoids.sh
```

which will first run the setoid repair tests contained within [`plugin/coq/ToSetoidTest.v`](plugin/coq/ToSetoidTest.v),then build the following two case studies:
- [`plugin/case-studies/grothendieck_int_equivalence_repair_tool.v`](plugin/case-studies/grothendieck_int_equivalence_repair_tool.v) (for the integer case study in Coq)
- [`plugin/case-studies/two_list_queue_equivalence_repair_tool.v`](plugin/case-studies/two_list_queue_equivalence_repair_tool.v) (for the queue case study in Coq)

The script will also build `plugin/case-studies/UIPList.v`, as a dependency of the queue case study. 
In our queue case study, we parameterize over lists/queues of type A, where UIP holds on A. `UIPList.v` proves that if UIP holds on A, it will hold on list A. 
We do not assume it for all types, so we are not adding an axiom to our theory. 

Note: we only support proper proof generation for unix-based systems in our extension to PUMPKIN Pi, since timeout are only supported in those instances.

## Cubical Agda Manual Case Studies
To run our Cubical Agda case studies, you should install [Cubical Agda](https://github.com/agda/cubical).
We tested our case studies on cubical library version v0.7, both with Agda version v2.6.4.1 on Ubuntu 24.04.2 and v2.6.4.3 on Ubuntu 22.04.5.

The main corresponding files for our case studies in Cubical Agda can be found in the following locations:
- [`plugin/case-studies/grothendieck_int_equiv.agda`](plugin/case-studies/grothendieck_int_equiv.agda) (for the integer case study in Cubical Agda)
- [`plugin/case-studies/equivalence_queue.agda`](plugin/case-studies/equivalence_queue.agda) (for the queue case study in Cubical Agda)
- [`plugin/case-studies/equivalence_int_abs.agda`](plugin/case-studies/equivalence_int_abs.agda) (for the internal proofs of correct repair in Cubical Agda). [`plugin/case-studies/alternateFunExtDep.agda`](plugin/case-studies/alternateFunExtDep.agda.agda) must be compiled prior.

## Using the Plugin

To repair across a setoid equivalence using this extension to PUMPKIN Pi, first the user must give a configuration. This involves four components:
- constructors, which are used to construct elements of the source type being repaired
- eliminators, which are used to eliminate elements of the source type being repaired
- iota-reduction rules, which are theorems stating how an application of an eliminator to a constuctor reduce
- eta-reduction rules. These are only supplied to the tool for historical reasons and likely unnecessary, and in practice we just use the identity function.

To initialize a setoid repair transformation, the user calls Save setoid, looking like this:

```Save setoid A B { promote = promote ; forget = forget ; types_a = typ1a typ2a; rels_a = rel1a rel2a; equiv_proofs_a = proof1a proof2a; types_b = typ1b typ2b ; rels_b = rel1b rel2b ; equiv_proofs_b = proof1b proof2b }.```

Here, `A` is the source type being repaired from, and `B` is the target type being repaired to. `promote` and `forget` are an equivalence between `A` and `B`. `types_a` is a space-delimited list of types which should be treated as setoids in the repair source. This tells PUMPKIN Pi to look for the equivalence relation instead of equality. `rels_a` is the equivalence relations on the types in `types_a`. `equiv_proofs_a` is a list of proofs that the relations in `rels_a` are equivalence relations, given as instances of the `Equivalence` type class. These terms must be given in the same order for all three lists, so `typ1a`, `rel1a`, and `proof1a` all go together. `types_b`, `rels_b`, and `equiv_proofs_b` serve the same function for the repair target `B`. This tells PUMPKIN Pi to repair equality or equvialence relations to the equivalence relation for that type instead of equality. This must be done for every type which is used as a setoid in both the source and target.

Then, the user runs 

```
Configure Lift A B {
    constrs_a = depConstrA1 depConstrA2 ;
    constrs_b = depConstrB1 depConstrB2 ;
    elim_a = depElimA1 depElimA2 ;
    elim_b = depElimB1 depElimB2 ;
    eta_a = etaA ;
    eta_b = etaB ;
    iota_a = iotaA1 iotaA2 ;
    iota_b = iotaB1 iotaB2
  }.
```

This tells PUMPKIN Pi that `depConstrA1` should be repaired to `depConstrB1`, and similarly for the other lists. It is possible to reconfigure PUMPKIN Pi to use a different set of eliminators. This is especially useful when eliminators need to have their motives specialized to provide additional data, such as a proof that motive is proper. We do this multiple times in our case studies.

Then, a term `trm` can be repaired by running

```
Lift A B in trm as repaired_trm.
```

The name of the repaired term will be `repaired_trm`. PUMPKIN Pi will also attempt to prove that `repaired_term` is proper with respect to the setoid of its output type, if `repaired_trm` is a function. This does not always work. Proofs that functions are proper are used when generating rewrites in terms that use those functions, so failing to prove a function proper may result in repair failing for terms downstream. In general, if PUMPKIN Pi fails to prove a function proper, and you do not prove it proper manually, you should accept that future calls to repair may fail.
