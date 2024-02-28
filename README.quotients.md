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
- `coq/playground/TwoListQueue/two_list_queue_equivalence_repair_tool.v` (for the queue case study in Coq)
- `coq/playground/grothendieck_int_equivalence_repair_tool.v` (for the integer case study in Coq)

The script will also build UIPList.v. 
In our queue case study, we parameterize over lists/queues of type A, where UIP holds on A. UIPList.v proves that if UIP holds on A, it will hold on list A. 
We do not assume it for all types, so we are not adding an axiom to our theory. 
