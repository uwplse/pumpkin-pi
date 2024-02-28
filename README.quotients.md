## Quotient Types Extension to Pumpkin Pi
This document describes the quotient types/setoids extension to the existing Pumpkin Pi infrastructure.
To fetch and build everything, make sure you have Coq 8.9.1 installed (later versions are not currently supported).

Then, to build everything, run:
```
cd plugin
./build.sh
```

To run the relevant case studies files, run:
```
./setoids.sh
```

which will build the following two case studies:
- [`coq/playground/grothendieck_int_equivalence_repair_tool.v`](coq/playground/grothendieck_int_equivalence_repair_tool.v) (for the integer case study in Coq)
- [`coq/playground/TwoListQueue/two_list_queue_equivalence_repair_tool.v`](coq/playground/TwoListQueue/two_list_queue_equivalence_repair_tool.v) (for the queue case study in Coq)

The script will also build `UIPList.v`. 
In our queue case study, we parameterize over lists/queues of type A, where UIP holds on A. `UIPList.v` proves that if UIP holds on A, it will hold on list A. 
We do not assume it for all types, so we are not adding an axiom to our theory. 

## Cubical Agda Manual Case Studies
To run our Cubical Agda case studies, you should install [Cubical Agda](https://github.com/agda/cubical)
The main corresponding files for our case studies in Cubical Agda can be found in the following locations:
- [`coq/playground/grothendieck_int_equiv.agda`](coq/playground/grothendieck_int_equiv.agda) (for the integer case study in Cubical Agda)
- [`coq/playground/equivalence_queue.agda`](coq/playground/equivalence_queue.agda) (for the queue case study in Cubical Agda)
