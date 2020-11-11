**NOTE FOR REVIEWERS: This is the generic README file for users.**
**This is not the guide mapping circled numbers in the paper to files.**
**That guide can be found in [GUIDE.md](./GUIDE.md).**

This is CARROT, a plugin for automatic discovery of and lifting across equivalences between types in Coq.
CARROT discovers the following type equivalence automatically:

1. **Algebraic Ornaments**: the type B (like `vector`) is the type A (like `list`) indexed by a fold
over A (like `length`)
2. **Records and Tuples**: the type A is a nested tuple of the form `x * (y * ...)`, and the type B is
a record with the same number of fields that have the same types
3. **Swapping and Renaming Constructors**: the types A and B are two inductive types that are equal up to
swapping constructor order and renaming constructors
4. **Escaping Sigma Types**: the type B (like `vector T n`) is the type A (like `{ s : sigT (vector T) & projT1 s = n}`) 
escaping the sigma type

It then ports functions and proofs across those equivalences.
For changes that don't fall into the above four buckets, you need to supply the equivalence yourself in a deconstructed form called a *configuration*.
The paper includes more information about this.
If you need help with this, please check out two examples: switching between unary and binary natural numbers [here](/plugin/coq/nonorn.v),
and an easier refactoring of constructors [here](/plugin/coq/playground/constr_refactor.v).

# Getting Started with CARROT

This section of the README is a getting started guide for users.
Please report any issues you encounter to GitHub issues, and please feel free to reach out with questions.

## Building CARROT

The only dependency you need to install yourself in order to use CARROT is Coq 8.8. 
CARROT also depends on a
[Coq plugin library](/plugin/src/coq-plugin-lib)
and on the [fix-to-elim](/plugin/deps/fix-to-elim) plugin, both of which are included. To build CARROT, run these commands:

```
cd plugin
./build.sh
```

## Using CARROT

For an overview of how to use the tool, see [Example.v](/plugin/coq/examples/Example.v)
and [minimal_records.v](/plugin/coq/minimal_records.v).

### Overview

At a high level, there are two main commands: `Find ornament` to search for equivalences (misleadingly named as an artifact of history and time constraints),
and `Lift` (or `Repair` for tactic support) to lift along those equivalences. `Find ornament` supports two additional options
to increase user confidence and to make the functions that it generates more useful.
If you skip running the `Find ornament` command and just run `Lift` or `Repair`,
then CARROT will run `Find ornament` for you automatically first.

In addition, there are a few commands that help make CARROT more useful: `Preprocess`
for pattern matching and fixpoint support, and `Unpack` to help recover more user-friendly types.
The `Preprocess` command comes from
[fix-to-elim](/plugin/deps/fix-to-elim).

#### Search

See [Search.v](/plugin/coq/examples/Search.v) for an example of search.

##### Command

```
Find ornament A B as A_to_B.
```

This command searches for the equivalence that describes the change from A to B, when the change is supported by automatic configuration.

##### Outputs 

For algebraic ornaments, `Find ornament` returns three functions if successful: 

1. `A_to_B`,
2. `A_to_B_inv`, and 
3. `A_to_B_index`.

`A_to_B` and `A_to_B_inv` form a specific equivalence, with `A_to_B_index` describing the fold over `A`.

For other kinds of equivalences, `Find ornament` returns only the first two of these.

##### Options for Correctness

`Find ornament` supports two options. 
By default, these options are disabled.
Together, setting these two options tells `Find ornament` to prove that its outputs are correct.

```
Set CARROT search prove coherence.
```

For algebraic ornaments, this option tells `Find ornament` to additionally generate a proof `A_to_B_coh` that shows that
`A_to_B_index` computes the left projection of applying `A_to_B`.

```
Set CARROT search prove equivalence.
```

This option tells `Find ornament` to generate proofs `A_to_B_section` and `A_to_B_retraction` that
prove that `A_to_B` and `A_to_B_inv` form an equivalence.

##### Using Custom Equivalences with Automatic Configuration

If `Find ornament` fails for an automatic configuration or you would like to use an existing equivalence, you can run this
command before lifting (still misleadingly named as an artifact of history and time constraints):

```
Save ornament A B { promote = f; forget = g}. 
```

where `f` and `g` form an equivalence that describes one of the supported relations between `A` and `B`.
Note that support for this is extremely experimental, and will not yet work if you try this with changes
not supported by automatic configuration (you will need manual configuration for that; more below).
You can find an example in [TestLift.v](/plugin/coq/TestLift.v).

You can also use this to substitute in a different equivalence for an existing equivalence, but again there
are some restrictions here on what is possible. See [ListToVectCustom.v](/plugin/coq/examples/ListToVectCustom.v)
for more information.

You can also skip one of promote or forget, provide just one, and let CARROT find the other for certain automatic configurations, for example:

```
Save ornament A B { promote = f }.
```

This is especially useful when there are many possible equivalences and you'd like to use a particular one,
but let CARROT figure out the rest. See [Swap.v](/plugin/coq/Swap.v) for examples of this.

##### Using Custom Equivalences with Manual Configuration

To use a custom equivalence not at all supported by one of the four search procedures, like switching between unary and binary natural numbers,
check out two examples [here](/plugin/coq/nonorn.v) and [here](/plugin/coq/playground/constr_refactor.v).
These examples set manual configuration and essentially skip the search procedure.
We will document them soon!
The paper says a lot about these but the examples are the best place to look for now.

##### Ambiguity 

Sometimes, automatic configuration of CARROT finds multiple possible equivalences. With swapping constructors in particular, there can
be an exponential number of possible equivalences.

In the case of ambiguity, CARROT presents up to the first 50 possible
options for the user (in a smart order), presents this as an error, and gives instructions for the user to
provide more information to `Find ornament` in the next iteration. If the equivalence you want is not in the
first 50 candidates, please use `Save ornament`. See [Swap.v](/plugin/coq/Swap.v) for examples of both of these.

##### Tactic Support

CARROT produces tactic suggestions for all proofs that `Find ornament` finds.
These are experimental, especially with dependent types, but may help you work with tactic proofs about equivalences.

#### Lift and Repair

See [Example.v](/plugin/coq/examples/Example.v), [minimal_records.v](/plugin/coq/minimal_records.v),
and [Swap.v](/plugin/coq/Swap.v) for examples of lifting.

##### Command

```
Lift A B in f as g. (* no tactic suggestions *)
Repair A B in f as g. (* tactic suggestions *)
``` 

This command lifts a function or proof `f` along the configured equivalence.
If you have already called `Find ornament` on `A` and `B`,
it will use the discovered equivalence.
If you have used manual configuration, it will use that configuration.
Otherwise, it will search for an equivalence first.

##### Outputs

`Lift` or `Repair` produces a term `g` which is the analogue of `f`, but refers to `B` in place of `A`.

##### Alternate Syntax

You can run this with an alternate syntax as well:


```
Lift A B in f as ..suffix.
Repair A B in f as ..suffix.
``` 

This will name the result `f_suffix`.

##### Whole Module Lifting

You can lift an endure module across an ornament all at the same time by running
this command:

```
Lift Module A B in Foo as Bar. (* no tactic suggestions *)
Repair Module A B in Foo as Bar. (* tactic suggestions *)
```

This will create a new module `Bar` with all of the liftings from `Foo`.

##### Tactic Support

Using `Repair` instead of `Lift` in thte above commands gives you tactic suggestions.
These tactic suggestions are experimental, but may help you with workflow integration.

To suggest decision procedures to try to improve tactic output, you can pass the `hint` option, like:

```
Repair Module A B in Foo as Bar { hint : "ring" "auto" }
```
This option comes after `opaque`, like:

```
Repair Module A B in Foo as Bar { opaque : A_rect B_rect; hint : "ring" "auto" }
```
At some point, we hope to make it possible to reuse the tactics from the original proof script easily,
even when they are not decision procedures.

##### Prettier Types

By default, CARROT lets Coq infer the types of lifted terms. You can 
instead tell CARROT to lift the types (these are typically prettier)
if you set the following function:

```
Set CARROT lift type.
```

##### Opaque Terms

If you'd like, you can tell the `Lift` or `Repair` command to treat certain terms as opaque
when you are positive that lifting them will have no effect:

```
Lift A B in f as g { opaque constant1 constant2 ... }.
Repair A B in f as g  { opaque constant1 constant2 ... }.
``` 

This can make lifting much faster.
It is **strongly advisable** to do this for certain terms that you know CARROT
should never reduce.
However, this can also cause unpredictable errors if your assumption is incorrect,
so be careful about your assumption.

You can also set a term to be globally opaque every time you lift between A and B
by using the following command:

```
Configure Lift A B { opaque constant1 constant2 ... }.
```

You can find an example of this in [more_records.v](/plugin/coq/more_records.v).

##### Caching

CARROT by default caches all lifted terms it encounters as it goes in order to save time.
You can disable this if you'd like by running this command:

```
Unset CARROT smart cache. 
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
for an example of this. See the [fix-to-elim](/plugin/deps/fix-to-elim) plugin
for more functionality for `Preprocess`.

##### Bonus Features for Algebraic Ornaments

When lifting across algebraic ornaments, to recover a slightly more user-friendly type for a lifted term `g`
with very little extra work, run:

```
Unpack g as g_u.
```

The type after `Unpack` still may not be very user-friendly.
If you would like to put in a little more work to get back types
that are very user friendly, check out the methodology in
[Example.v](/plugin/coq/examples/Example.v). The key is to
set the following option:

```
Set CARROT search smart eliminators.
```

This generates a useful induction principle. Using that induction princple and composing
this by lifting across another equivalence, you can get from your unlifted type A to B at a
particular index, with much nicer type signatures.

CARROT makes the same assumptions about types for search for algebraic ornaments that DEVOID makes.

### Known Issues

Please see our GitHub issues (redacted) before reporting a bug
(though please do report any bugs not listed there).

One outstanding issue (an unimplemented optimization) has consequences for how we lift and unpack large
constants compositionally. For now, for large constants, you should prefer lifting several times and then unpacking
the result several times over iteratively lifting and unpacking. See this issue (redacted).

# Implementation and Development

Transparency is very important to me and my coauthors. My goal is not just to produce a useful a tool,
but also to demonstrate ideas that other people can use in their tools.

This part of the README is here to complement that. It describes the structure of the code a bit. It should also help if you are interested in contributing
to CARROT, or if you are interested in using some of the libraries from CARROT in your code.

## Understanding the Code

This is an outline of the structure of the code. Please cut an issue if you are confused about anything here.
Please also feel free to ask if you are confused about anything that the code does.
Note that this may not be fully up-to-date right now because I am tired and the world is collapsing and so on,
though slightly less in some respects (more in others) than it was a few weeks ago so that's nice I guess.
Reivewers should use the map in [GUIDE.md](./GUIDE.md) to find things from the paper and not this.

* [LICENSE](/LICENSE): License
* [plugin](/plugin): Main directory for the plugin
  - [build.sh](/plugin/coq/build.sh): Build script
  - [test.sh](/plugin/coq/test.sh): Test script
  - [coq](/plugin/coq): Tests and paper examples
    - [examples](/plugin/coq/examples): Paper examples (see paper examples section of this document for details)
    - [playground](/plugin/coq/playground): Preliminary thoughts on useful theory for later extensions to CARROT
    - [Indtype.v](/plugin/coq/Indtype.v): Lifting tests for inductive relations
    - [Infrastructure.v](/plugin/coq/Infrastructure.v): Testing infrastructure
    - [ShouldFail.v](/plugin/coq/ShouldFail.v): Tests that should currently fail
    - [Test.v](/plugin/coq/Test.v): Tests for search for algebraic ornaments
    - [TestLift.v](/plugin/coq/TestLift.v): Tests for lifting across algebraic ornaments
    - [TestUnpack.v](/plugin/coq/TestUnpack.v): Tests for unpacking indexed types
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
    - [main.v](/plugin/eval/main.v): DEVOID case study code (for regression testing of algebraic ornaments)
    - [times.sed](/plugin/eval/times.sed): Script to format times
    - [together.sh](/plugin/eval/together.sh): Main case study script
  - [deps](/plugin/deps): Depedencies
    - [fix-to-elim](/plugin/src/fix-to-elim): **Preprocessing**
  - [src](/plugin/src): Source directory
    - [coq-plugin-lib](/plugin/src/coq-plugin-lib): Coq plugin library
    - [lib](/plugin/src/lib): Internal library
    - [automation](/plugin/src/automation): Automation directory
      - [search](/plugin/src/automation/search): **Search**
      - [lift](/plugin/src/automation/lift): **Lifting**
      - [unpack.ml](/plugin/src/automation/unpack.ml) and [unpack.mli](/plugin/src/automation/unpack.mli): Converting the unpacking tactic to a command
      - [depelim.ml](/plugin/src/automation/depelim.ml) and [depelim.mli](/plugin/src/automation/depelim.mli): Automation for non-primitive projections
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
  - [theories](/plugin/theories): CARROT theories
    - [Adjoint.v](/plugin/theories/Adjoint.v): Turning equivalences into adjoint equivalences
    - [Prod.v](/plugin/theories/Prod.v): Preprocessed projections of pairs
    - [Eliminators.v](/plugin/theories/Eliminators.v): **Generalized smart eliminators for user-friendly types**
    - [Ornaments.v](/plugin/theories/Ornaments.v): Loader theory for CARROT
    - [Unpack.v](/plugin/theories/Unpack.v): **Unpacking terms** (Ltac tactic)
* [.gitignore](/.gitignore)
* [README.md](/README.md)

## Regression Testing

The test script in the [plugin](/plugin) directory runs all of the regression tests:

```
./test.sh
```

After making a change to CARROT, you should always run this. You should
also run the case study scripts to check performance.

## Licensing and Attribution

CARROT is MIT licensed, since I have a very strong preference for the MIT license and
since I believe I do not need to use Coq's LGPL when writing language plugins.
This interpretation might be wrong, though, so I suppose you should tread lightly.
If you are an expert in licensing, definitely let me know if this is wrong.

Regardless, I would like CARROT to be used freely by anyone for any purpose.
All I ask for is attribution, especially in any papers that you publish that use CARROT
or any of its code. Please cite the paper when referring to CARROT in those papers.

