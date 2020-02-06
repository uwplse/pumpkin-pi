This is DEVOID, a plugin for automatic discovery of and lifting across 
certain equivalences between types in Coq. It began as the artifact for the ITP paper [Ornaments for Proof Reuse in Coq](http://tlringer.github.io/pdf/ornpaper.pdf), but has since been extended.
Please cite this paper when referring to DEVOID. A version of DEVOID that corresponds to the
ITP camera-ready can be found in [this release](http://github.com/uwplse/ornamental-search/releases/tag/itp+equiv).

Basically, when you have two types A and B that are related in certain ways, DEVOID can search for
and prove the relation between those types, then lift functions and proofs between them.
The following relations are currently supported:

1. **Algebraic Ornaments**: the type B (like `vector`) is the type A (like `list`) indexed by a fold
over A (like `length`)
2. **Records and Tuples**: the type A is a nested tuple of the form `x * (y * ...)`, and the type B is
a record with the same number of fields that have the same types

DEVOID is a part of the [PUMPKIN PATCH](https://github.com/uwplse/PUMPKIN-PATCH) 
proof repair plugin suite, and is included as a dependency of PUMPKIN PATCH
starting with release 0.1.

# Getting Started with DEVOID

This section of the README is a getting started guide for users.
Please report any issues you encounter to GitHub issues, and please feel free to reach out with questions.

## Building DEVOID

The only dependency you need to install yourself in order to use DEVOID is Coq 8.8. 
DEVOID also depends on a
[Coq plugin library](https://github.com/uwplse/coq-plugin-lib) which is included
as a submodule automatically in the build script,
and on the [fix-to-elim](https://github.com/uwplse/fix-to-elim) plugin, which is also included. To build DEVOID, run these commands:

```
cd plugin
./build.sh
```

## Using DEVOID

For an overview of how to use the tool, see [Example.v](/plugin/coq/examples/Example.v)
and [minimal_records.v](/plugin/coq/minimal_records.v).

### Overview

At a high level, there are two main commands: `Find ornament` to search for ornaments,
and `Lift` to lift along those ornaments. `Find ornament` supports two additional options
to increase user confidence and to make the functions that it generates more useful.
If you skip running the `Find ornament` command and just run `Lift`,
then DEVOID will run `Find ornament` for you automatically first.

In addition, there are a few commands that help make DEVOID more useful: `Preprocess`
for pattern matching and fixpoint support, and `Unpack` to help recover more user-friendly types.
The `Preprocess` command comes from our plugin
[fix-to-elim](https://github.com/uwplse/coq-plugin-lib).
There is also work in progress on a general methodology (which will hopefully be automated in
the future) to get even more user-friendly types.

#### Search

See [Search.v](coq/examples/Search.v) for an example of search.

##### Command

```
Find ornament A B as A_to_B.
```

This command searches for the relation between A and B.

##### Outputs 

For algebraic ornaments, `Find ornament` returns three functions if successful: 

1. `A_to_B`,
2. `A_to_B_inv`, and 
3. `A_to_B_index`.

`A_to_B` and `A_to_B_inv` form a specific equivalence, with `A_to_B_index` describing the fold over `A`.

For records and products, `Find ornament` returns only the first two of these.

##### Options for Correctness

`Find ornament` supports two options. 
By default, these options are disabled.
Together, setting these two options tells `Find ornament` to prove that its outputs are correct.

```
Set DEVOID search prove coherence.
```

For algebraic ornaments, this option tells `Find ornament` to additionally generate a proof `A_to_B_coh` that shows that
`A_to_B_index` computes the left projection of applying `A_to_B`.

```
Set DEVOID search prove equivalence.
```

This option tells `Find ornament` to generate proofs `A_to_B_section` and `A_to_B_retraction` that
prove that `A_to_B` and `A_to_B_inv` form an equivalence.

##### Using Custom Equivalences

If `Find ornament` fails or you would like to use an existing equivalence, you can run this
command before lifting:

```
Save ornament A B { promote = f; forget = g}. 
```

where `f` and `g` form an equivalence that describes one of the supported relations between `A` and `B`.
Note that support for this is extremely experimental, and will not yet work if you try this with unsupported
relations. You can find an example in [TestLift.v](/plugin/coq/TestLift.v).

#### Lift

See [Example.v](/plugin/coq/examples/Example.v) and [minimal_records.v](/plugin/coq/minimal_records.v) for
examples of lifting.

##### Command

```
Lift A B in f as g.
``` 

This command lifts a function or proof `f` along the discovered relation.
DEVOID must be able to find an ornament between `A` and `B` for this
command to work. If you have already called `Find ornament` on `A` and `B`,
it will use the discovered ornament; otherwise, it will search for an
ornament first.

##### Outputs

`Lift` produces a function `g` which is the analogue of `f`.

##### Alternate Syntax

You can run this with an alternate syntax as well:


```
Lift A B in f as ..suffix.
``` 

This will name the result `f_suffix`.

##### Whole Module Lifting

You can lift an endure module across an ornament all at the same time by running
this command:

```
Lift Module A B in Foo as Bar.
```

This will create a new module `Bar` with all of the liftings from `Foo`.

##### Prettier Types

By default, DEVOID lets Coq infer the types of lifted terms. You can 
instead tell DEVOID to lift the types (these are typically prettier)
if you set the following function:

```
Set DEVOID lift type.
```

##### Opaque Terms

If you'd like, you can tell the `Lift` command to treat certain terms as opaque
when you are positive that lifting them will have no effect:

```
Lift A B in f as g { opaque constant1 constant2 ... }.
``` 

This can make lifting faster.
However, it can also cause unpredictable errors if your assumption is incorrect.

You can also set a term to be globally opaque every time you lift between A and B
by using the following command:

```
Configure Lift A B { opaque constant1 constant2 ... }.
```

You can find an example of this in [more_records.v](/plugin/coq/more_records.v).

##### Caching

DEVOID by default caches all lifted terms it encounters as it goes in order to save time.
You can disable this if you'd like by running this command:

```
Unset DEVOID smart cache. 
```

#### Additional Functionality

This functionality is demonstrated in [Example.v](/plugin/coq/examples/Example.v).

##### Preprocess

The `Lift` command does not support pattern matching and fixpoints directly.
To lift a function `f'` that uses pattern matching and (certain) fixpoints, run:

```
Preprocess f' as f.
```

Then, run:

```
Lift A B in f as g.
```

You can also run `Preprocess` on an entire module; see [ListToVect.v](/plugin/coq/examples/ListToVect.v)
for an example of this.

##### Unpack

To recover a slightly more user-friendly type for a lifted term `g`, run:

```
Unpack g as g_u.
```

##### User-Friendly Types

The type after `Unpack` still may not be very user-friendly.
[Example.v](/plugin/coq/examples/Example.v) describes how to recover
even more user-friendly types for lifted terms.

For the status of a general methodology for this,
see [GitHub issue #39](http://github.com/uwplse/ornamental-search/issues/39).

### Assumptions

DEVOID makes some assumptions about your terms and types for now (described in Section 3 of the paper).
[Assumptions.v](/plugin/coq/examples/Assumptions.v) describes these assumptions in more detail
and gives examples of unsupported terms and types.
Note that the assumptions for records and tuples are not yet documented, since
support for those types is brand new.

These assumptions are mostly to simplify search. We hope to loosen them eventually.
If any are an immediate inconvenience to you, then please cut a GitHub issue with an example
you would like to see supported so that we can prioritize accordingly.

### Known Issues

Please see our GitHub [issues](https://github.com/uwplse/ornamental-search/issues) before reporting a bug
(though please do report any bugs not listed there).

One outstanding issue (an unimplemented optimization) has consequences for how we lift and unpack large
constants compositionally. For now, for large constants, you should prefer lifting several times and then unpacking
the result several times over iteratively lifting and unpacking. See [this issue](https://github.com/uwplse/ornamental-search/issues/44).

# Examples

This part of the README explains the examples and how they correspond to the paper.
You may find these useful as a user, as a reader, or as a developer.

## Paper Examples

The example from the paper are in the [examples](/plugin/coq/examples) directory.
Here is an overview of the examples, in order of relevance to the paper:

* [Intro.v](/plugin/coq/examples/Intro.v): Examples from Section 1 of the paper
* [Example.v](/plugin/coq/examples/Example.v): Motivating example from Section 2 of the paper
* [Assumptions.v](/plugin/coq/examples/Assumptions.v): Assumptions from Section 3 of the paper
* [LiftSpec.v](/plugin/coq/examples/LiftSpec.v): Intuition for lifting from Section 3 of the paper
* [Search.v](/plugin/coq/examples/Search.v): Search examples from Section 4 of the paper
* [Lift.v](/plugin/coq/examples/Lift.v): Lifting examples from Section 4 of the paper
* [ListToVect.v](/plugin/coq/examples/ListToVect.v): Example of preprocessing a module from Section 5 of the paper
* [Projections.v](/plugin/coq/examples/Projections.v): Evidence for non-primitive projection claims from Section 5 of the paper

## Tuple and Record Examples

The most useful examples of lifting between tuples and records are in [minimal_records.v](/plugin/coq/minimal_records.v)
and [more_records.v](/plugin/coq/more_records.v).

## Other Examples

The [coq](/plugin/coq) directory has more examples.
These examples are regression tests, and so are not guaranteed to be useful
to users. However, if you would like more examples, you may look there as well.

The [eval](/plugin/eval) directory has examples from the case study from Section 6 of the paper.
They may be a bit hard to read since there is some scripting going on.
They may still be interesting to you whether or not you want to actually run the case study.

# Case Study

This section of the README describes how to reproduce the case study from Section 4 of the paper.
The case study is in the [eval](/plugin/eval) directory.
We support the case study scripts on only Linux right now.

## Building the Case Study Code

To run the case study code, you need the following additional dependencies:
* The Equivalences for Free! [univalent parametricity framework](https://github.com/CoqHott/univalent_parametricity) (hereon EFF)
* [Datamash](https://www.gnu.org/software/datamash/)

Run the following to make EFF:

```
cd <path-to-EFF>
make && make install
```

Datamash should install in a straightforward way from a package manager using the link above.

## Reproducing the Paper Case Study

The particular commit for EFF used for the results in the paper is [this commit](https://github.com/CoqHott/univalent_parametricity/tree/02383400c2711a1de1581e62e0a463759211d4df). We have rerun the experiments using 
[this commit](https://github.com/CoqHott/univalent_parametricity/tree/993ec06760953331c588b47ba4ad423f7d2c0c46), 
the newest commit at the time of release, and there results have not changed significantly. Results are not guaranteed to
be the same for different commits of EFF, especially later ones which may include optimizations not yet implemented
at the time of writing. Similarly, on different architectures, the numbers may be slightly different; the orders of 
magnitude should be comparable.

Enter the [eval](/plugin/eval) directory:

```
cd eval
```

Increase your stack size:

```
ulimit -s 100000
```

Run the following script:

```
./together.sh
```

The script takes a while, as it runs each function ten times each
on large data both for DEVOID and for EFF.
When it is done, check the `results` folder for the median runtimes as well as the size of reduced functions.
This also does a sanity check to make sure both versions of the code produce the same output.
It does not yet try to reduce the proof of `pre_permutes` using EFF,
otherwise the case study would take a very long time to run.
To run this just once, enter the [equiv4free](/plugin/eval/equiv4free) directory:

```
cd equiv4free
```

In that directory, uncomment the following line in [main.v](/plugin/eval/equiv4free/main.v):

```
(*Redirect "../out/normalized/pre_permutes-sizedEFFequiv" Eval compute in pre_permutes'.*)
```

Then run the following script, which runs the EFF code just once:

```
./prepermutes.sh
```

This should take a while (how long depends on your architecture) and produce a very large term.

## Understanding the Case Study Code

The code for the case study is in the [eval](/plugin/eval) folder.
The case study uses the same exact input datatypes for both DEVOID and EFF,
copying and pasting in the inputs, lifted functions, and equivalences DEVOID produces to run on the dependencies of EFF.
The reasons for copying the inputs are that EFF has different
Coq dependencies, so the base functions perform differently. In addition, lifting constants with EFF additionally slows down 
performance, and we would like to control for only the performance of lifted functions, which is easiest to understand.

There is one other thing worth understanding about the case study code.
We used to use this command to measure the performance of `foo`:

```
Eval vm_compute in foo.
```

An ITP reviewer noted that this includes the amount of time to print `foo`. This is a lot of
overhead that clouds the usefulness of the data. The reviewer suggested writing:

```
Eval vm_compute in (let _ := foo in tt).
```

Unfortunately, Coq seems to be a bit too smart for that; it doesn't actually bother computing `foo`
if you do that. Instead, we now write:

```
Eval vm_compute in (List.tl [foo]).
```

This forces Coq to compute `foo`, but ultimately prints `[]`, thereby not adding printing time.
It does add the time to run `List.tl`, but this overhead is very minimal on a list of a single element
(much more minimal than the overhead of printing).

# Implementation and Development

Transparency is very important to me and my coauthors. My goal is not just to produce a useful a tool,
but also to demonstrate ideas that other people can use in their tools.

Some information for transparency is in the paper:
Section 4 discusses the core algorithms that DEVOID implements, and
section 5 discusses a sample of implementation challenges.

This part of the README is here to complement that. It describes the structure of the code a bit. It should also help if you are interested in contributing
to DEVOID, or if you are interested in using some of the libraries from DEVOID in your code.

## Understanding the Code

This is an outline of the structure of the code. Please cut an issue if you are confused about anything here.
Please also feel free to ask if you are confused about anything that the code does.

* [LICENSE](/LICENSE): License
* [plugin](/plugin): Main directory for the plugin
  - [build.sh](/plugin/coq/build.sh): Build script
  - [test.sh](/plugin/coq/test.sh): Test script
  - [coq](/plugin/coq): Tests and paper examples
    - [examples](/plugin/coq/examples): Paper examples (see paper examples section of this document for details)
      - [Intro.v](/plugin/coq/examples/Intro.v)
      - [Example.v](/plugin/coq/examples/Example.v)
      - [Assumptions.v](/plugin/coq/examples/Assumptions.v)
      - [LiftSpec.v](/plugin/coq/examples/LiftSpec.v)
      - [Search.v](/plugin/coq/examples/Search.v)
      - [Lift.v](/plugin/coq/examples/Lift.v)
      - [ListToVect.v](/plugin/coq/examples/ListToVect.v)
      - [Projections.v](/plugin/coq/examples/Projections.v)
    - [Indtype.v](/plugin/coq/Indtype.v): Lifting tests for inductive relations
    - [Infrastructure.v](/plugin/coq/Infrastructure.v): Testing infrastructure
    - [ShouldFail.v](/plugin/coq/ShouldFail.v): Tests that should currently fail
    - [Test.v](/plugin/coq/Test.v): Tests for search for algebraic ornaments
    - [TestLift.v](/plugin/coq/TestLift.v): Tests for lifting across algebraic ornmanets
    - [minimal_records.v](/plugin/coq/minimal_records.v): Basic tests for products and records
    - [more_records.v](/plugin/coq/more_records.v): More advanced tests for products and records
    - [NoSmartCache.v](/plugin/coq/NoSmartCache.v): Disabling the smart cache
    - [SmartCache.v](/plugin/coq/SmartCache.v): Keeping the smart cache enabled
    - [prod_rect.v](/plugin/coq/prod_rect.v): Test functionality that produces prettier terms
  - [eval](/plugin/eval): Case study code and dependencies
    - [equiv4free](/plugin/eval/equiv4free): EFF case study code and depedencies
      - [Makefile](/plugin/eval/equiv4free/Makefile)
      - [cast.v](/plugin/eval/equiv4free/cast.v)
      - [lemmas.v](/plugin/eval/equiv4free/lemmas.v)
      - [list.v](/plugin/eval/equiv4free/list.v)
      - [main.v](/plugin/eval/equiv4free): Main EFF case study code
      - [perm.v](/plugin/eval/equiv4free)
      - [prepermutes.sh](/plugin/eval/equiv4free/prepermutes.sh): Script to normalize `pre_permutes`
    - [Makefile](/plugin/eval/Makefile)
    - [cast.v](/plugin/eval/cast.v)
    - [lemmas.v](/plugin/eval/lemmas.v)
    - [main.v](/plugin/eval/main.v): Main DEVOID case study code
    - [times.sed](/plugin/eval/times.sed): Script to format times
    - [together.sh](/plugin/eval/together.sh): Main case study script
  - [deps](/plugin/deps): Depedencies
    - [fix-to-elim](/plugin/src/fix-to-elim): **Preprocessing** with the [fix-to-elim](https://github.com/uwplse/coq-plugin-lib) plugin
  - [src](/plugin/src): Source directory
    - [coq-plugin-lib](/plugin/src/coq-plugin-lib): [Coq plugin library](https://github.com/uwplse/coq-plugin-lib)
    - [lib](/plugin/src/lib): Internal library
    - [automation](/plugin/src/automation): Automation directory
      - [coherence.ml](/plugin/src/automation/coherence.ml) and [coherence.mli](/plugin/src/automation/coherence.mli): **Proving coherence**
      - [equivalence.ml](/plugin/src/automation/equivalence.ml) and [equivalence.mli](/plugin/src/automation/equivalence.mli): **Proving section and retraction**
      - [eta.ml](/plugin/src/automation/eta.ml) and [eta.mli](/plugin/src/automation/eta.mli): Automation for non-primitive projections
      - [search.ml](/plugin/src/automation/search.ml) and [search.mli](/plugin/src/automation/search.mli): **Searching for ornaments**
      - [lift](/plugin/src/automation/lift): **Lifting terms**
      - [unpack.ml](/plugin/src/automation/unpack.ml) and [unpack.mli](/plugin/src/automation/unpack.mli): Converting the unpacking tactic to a command
    - [cache](/plugin/src/cache): Caching ornaments and lifted terms
      - [caching.ml](/plugin/src/cache/caching.ml) and [caching.mli](/plugin/src/cache/caching.mli)
    - [components](/plugin/src/components): Components in the style of [PUMPKIN PATCH](http://tlringer.github.io/pdf/pumpkinpaper.pdf)
      - [abstraction.ml](/plugin/src/components/abstraction.ml) and [abstraction.mli](/plugin/src/components/abstraction.mli): 
      - [differencing.ml](differencing.ml) and [differencing.mli](/plugin/src/components/differencing.mli): 
      - [factoring.ml](/plugin/src/components/factoring.ml) and [factoring.mli](/plugin/src/components/factoring.mli): 
      - [specialization.ml](/plugin/src/components/specialization.ml) and [specialization.mli](/plugin/src/components/specialization.mli): 
    - [ornaments](/plugin/src/ornaments): Internal representations and configuration
    - [frontend.ml](/plugin/src/frontend.ml) and [frontend.mli](/plugin/src/frontend.mli): Main functionality for commands
    - [options.ml](/plugin/src/options.ml) and [options.mli](/plugin/src/options.mli): Definitions of and access to options
    - [ornamental.ml4](/plugin/src/ornamental.ml4): **Top-level source file**
    - [ornaments.mlpack](/plugin/src/ornaments.mlpack)
  - [theories](/plugin/theories): DEVOID theories
    - [Adjoint.v](/plugin/theories/Adjoint.v): Turning equivalences into adjoint equivalences
    - [Prod.v](/plugin/theories/Prod.v): Preprocessed projections of pairs
    - [Ornaments.v](/plugin/theories/Ornaments.v): Loader theory for DEVOID
    - [Unpack.v](/plugin/theories/Unpack.v): **Unpacking terms** (Ltac tactic)
* [.gitignore](/.gitignore)
* [README.md](/README.md)

## Regression Testing

The test script in the [plugin](/plugin) directory runs all of the regression tests:

```
./test.sh
```

After making a change to DEVOID, you should always run this. You should
also run the case study scripts to check performance.

## Licensing and Attribution

DEVOID is MIT licensed, since I have a very strong preference for the MIT license and
since I believe I do not need to use Coq's LGPL when writing language plugins.
This interpretation might be wrong, though, so I suppose you should tread lightly.
If you are an expert in licensing, definitely let me know if this is wrong.

Regardless, I would like DEVOID to be used freely by anyone for any purpose.
All I ask for is attribution, especially in any papers that you publish that use DEVOID
or any of its code. Please cite the ITP paper when referring to DEVOID in those papers.

