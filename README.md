## Dependencies

The only dependency to use the plugin is Coq 8.8.

To run the case study code, you also need the
univalent parametricity framework: https://github.com/CoqHott/univalent_parametricity

## Building

### Plugin

```
coq_makefile -f _CoqProject -o Makefile
make && make install
```

### Case Study Dependencies

```
cd <path-to-univalent-parametricity>
coq_makefile -f _CoqProject -o Makefile
make && make install
```

## Understanding the Code

The top-level is in `ornamental.ml4`, which outsources to `frontend.ml`. From there, the two major functionalities
are the search algorithm in `automation/search` and the lifting algorithm in `automation/lift`. A description
of these implementations can be found in Sections 5.1.1 and 5.1.2 of the paper; the relevant theory behind these is in
Sections 3.2, 4.1, and Appendix A.2. Please ping me if you have any questions, or create an issue so that I can
patch up the code to better correspond to the paper.

## Running

### Tests

The test script runs all tests:

```
./test.sh
```

### Case Study Code

The case study script updates the functions in the case study code, then runs the case studies:

```
./TODO.sh
```

