DEVOID is a plugin for automatic discovery of and lifting across 
algebraic ornaments in Coq. Basically, when you have two types
A and B, where B is A indexed by some new type that is determined
by a fold over A, DEVOID can search for the fold and functions
that relate A and B, and then lift functions and proofs between types.
The produced functions and proofs are usually about as fast as the origial.
See the examples for more detail. 

Note that DEVOID makes some additional assumptions about the syntax of your types for now,
in particular that both types have the same number of contructors in the same order,
and that there is one new hypothesis for each new index of each inductive hypothesis in B. 
These restrictons are mostly for search. We hope to loosen them eventually.

## Dependencies

The only dependency to use the plugin is Coq 8.8.

To run the case study code, you also need the following:
* The Equivalences for Free! [univalent parametricity framework](https://github.com/CoqHott/univalent_parametricity)
* [Datamash](https://www.gnu.org/software/datamash/)

## Building

### Plugin

```
coq_makefile -f _CoqProject -o Makefile
make && make install
```

### Case Study Dependencies

Run the following to make the Equivalences for Free! univalent parametricity framework:

```
cd <path-to-univalent-parametricity>
make && make install
```

Datamash should install in a straightforward way from a package manager using the link above.

## Running

For a complete overview of how to use the tool, see `coq/examples/Example.v`. At a high level,
there are two main commands:

`Find ornament A B as A_to_B.`: Search for the relation that describes the algebraic ornament
between A and B, and return three functions if successful: `A_to_B`, `A_to_B_inv`, and `A_to_B_index`.
`A_to_B` and `A_to_B_inv` form a specific equivalence, with `A_to_B_index` describing the fold over `A`.
See `coq/examples/Search.v` for an example of this on lists and vectors.

`Lift A B in f as g.`: Lift a function along the discovered relation. See `coq/examples/Lift.v` for a few examples
of how this works.

There are two additional commands: `Preprocess` to preprocess terms for lifting,
and `Unpack` to give you back types that are a little bit better than the automatically
generated types. There is a methodology outlined in `coq/examples/Example.v` for recovering
even more useful types.

### Known Issues

Please see our GitHub [issues](https://github.com/uwplse/ornamental-search/issues) before reporting a bug
(though please do report any bugs not listed there). The most significant bug for user experience right now
is that the plugin currently fails with asynchronous processing in CoqIDE. So if you would like to use the 
plugin in CoqIDE, either turn off asynchronous processing, or step through your file one command at a time.
Otherwise, you will likely get a `Not_found` error.

### Tests

The test script runs all tests:

```
./test.sh
```

### Examples

The example from the paper are in the `coq/example` directory. It is best to step through these one by one.

### Case Study Code

We only support the case study scripts on Linux right now.

There are two ways to run the case study, in two different scripts.
The reason for the two different versions is that the Equivalences for Free! univalent parametricity framework (hereon EFF) has different
Coq dependencies, so the base functions perform differently. 
The first way uses the same exact input datatypes for both DEVOID and EFF,
copying and pasting in the lifted functions DEVOID produces to run on the dependencies of EFF;
This is the version that the paper uses, as the results it produces are the easiest to understand,
since there are not different base numbers for each tool; all terms are normalized with the same
set of dependencies.
The second way does all of the lifting from scratch with
the base datatypes in both the DEVOID code and EFF;
these results are more difficult to interpret, and is not the version in the paper.

Each of these scripts takes a while, as it runs each function ten times each
on large data both for DEVOID and for EFF.

#### Reproducing the Paper Case Study

The particular commit for EFF used for the results in the paper is [this commit](https://github.com/CoqHott/univalent_parametricity/tree/02383400c2711a1de1581e62e0a463759211d4df). We have rerun the experiments using 
[this commit](https://github.com/CoqHott/univalent_parametricity/tree/993ec06760953331c588b47ba4ad423f7d2c0c46), 
the newest commit at the time of release, and there results have not changed significantly. Results are not guaranteed to
be the same for different commits of EFF, especially later ones which may include optimizations not yet implemented
at the time of writing. Similarly, on different architectures, the numbers may be slightly different; the orders of 
magnitude should be comparable.

Enter the `eval` directory:

``
cd eval
``

Run the following script:

```
./together.sh
```

Then check the `together` folder for the median runtimes as well as the size of reduced functions.
This also does a sanity check to make sure both versions of the code produce the same output.
It does not yet try to reduce the proof that timed out with EFF after an hour (it reduces it with DEVOID, but not with EFF),
otherwise the case study would take ten hours to run. To run this just once, enter the `equiv4free` directory:

``
cd equiv4free
``

In that directory, uncomment the following line in `main.v`:

```
(*Redirect "../out/normalized/pre_permutes-sizedEFF" Eval compute in pre_permutes'.*)
```

Then run the following script, which runs the EFF code just once with a timeout:

```
./prepermutes.sh
```

The timeout is an hour, so grab a coffee or read a book or something. It should timeout,
or finish normalizing very close to the timeout limit (if so, the script will record how long it took).
If your computer does not have a lot of memory, you may run out of memory first.

#### Using Different Datatypes

This is not in the paper, but you might be curious for the sake of validity whether the same benefits apply
lifting the datatypes separately from scratch. To see that they do, run the second version, run the following script:

```
./separate.sh
```

Then check the `separate` folder for the results.

## Understanding the Code

The top-level is in `ornamental.ml4`, which outsources to `frontend.ml`. From there, the two major functionalities
are the search algorithm in `automation/search` and the lifting algorithm in `automation/lift`. Please ping me if you have any questions, 
or create an issue so that I can patch up the code to better correspond to the paper.





