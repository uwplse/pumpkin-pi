Welcome, reviewers! This is the guide that maps circled numbers in the paper to locations in the anonymized code.
It includes some notes about the code when relevant.

# 1

**Location**: [Swap.v](/plugin/coq/Swap.v).

**Notes**: This file contains a number of different examples, some referenced in the paper and some not.
These are all documented for your convenience.

# 2

**Location**: [constr_refactor.v](/plugin/coq/playground/constr_refactor.v).

**Notes**: None.

# 3

**Location**: [Example.v](/plugin/coq/examples/Example.v).

**Notes**: This example is based on the example from DEVOID, and spans two case studies.
We have documented this extensively, including what is unique to CARROT.

# 4

**Location**: [lift.ml](/plugin/src/automation/lift/lift.ml).

**Notes**: Some of the comments are out of sync with the paper. We apologize for that.
You will also see more rules than there are in the transformation in the paper;
those extra rules are optimizations, and are partially discussed in the implementation section of the paper.

# 5

**Location**: [nonorn.v](/plugin/coq/nonorn.v).

**Notes**: There is a bug with universes. This is noted in the code and the workaround is explained.
It is not theoretically interesting.

# 6

**Location**: [liftconfig.ml](/plugin/src/automation/lift/liftconfig.ml).

**Notes**: The bridge between this and [lift.ml](/plugin/src/automation/lift/lift.ml) is [liftrules.ml](/plugin/src/automation/lift/liftrules.ml).
This file is a bit out of sync with the paper terminology.
Unification heuristics typically start with "applies" or "is."
A lot of the extras you see in there are for optimizations, or to improve the quality of produced code.
When iota is trivial over both A and B, I sometimes take shortcuts and don't return the real iota.
There are probably a few other shortcuts in there, and those may not always be well documented.
The other weird thing is that, as an artifact of development history, the current search procedures 
start by finding the equivialence and deriving a configuration from that, rather than the other way around.
More on that later.

# 7

**Location**: [refine_unit.v](/plugin/coq/playground/refine_unit.v).

**Notes**: This is just easier to understand in Coq than in English.

# 8

**Location**: [arbitrary.v](/plugin/coq/playground/arbitrary.v).

**Notes**: This proof is well documented in the code, but essentially you will see a generic construction for a configuration from an equivalence.
This configuration is not always the best configuration to actually use, though late in the file we explain the relationship
between this generic construction more desirable ones.
We did not want to depend on HoTT or on univalent parametricity, so we unfolded the definition of transport and instantiated it to the terms
we were proving things about.
All proofs in this file go through without any axioms. 
The big and interesting step is to use the adjunction property of equivalences (no axioms needed for that property).

# 9

**Location**: [search.ml](/plugin/src/automation/search/search.ml).

**Notes**: Back to the weird part I mentioned when discussing file 6.
As an artifact of history, we find equivalences first, then derive configurations, rather than the other way around.
So the word "essentially" in the paper is important.
We do use the paper algorithm, but the paper algorithm is the idealized post-hoc description of the thing we did in a more ad-hoc manner originally.
Also as mentioned in the paper, we don't describe these in detail, but the code should help with understanding the way that they work.
The algebraic ornaments search procedure comes from DEVOID; all others are CARROT-specific.

# 10

**Location**: [equivalence.ml](/plugin/src/automation/search/equivalence.ml).

**Notes**: All of the notes from file 9 apply here as well.

# 11

**Location**: [decompiler.ml](/plugin/src/coq-plugin-lib/src/coq/decompiler/decompiler.ml).

**Notes**: Fairly self-descriptive. A decompiler like the mini decompiler but with the discussed implementation differences.

# 12

**Location**: [liftrules.ml](/plugin/src/automation/lift/liftrules.ml).

**Notes**: This file contains more than just the termination checks, but you can find those there.
The termination checks are super heuristic and will not always work.
We discuss this in the future work section.

# 13

**Location**: [minimal_records.v](/plugin/coq/minimal_records.v).

**Notes**: This is a minimized version of the problem that the proof engineer ran into.
Essentially there is a way around this problem, but it is not ideal.
The ideal would be type-directed search.
The redacted blog post discusses that, as does the future work section.

# 14

**Location**: [caching.ml](/plugin/src/cache/caching.ml).

**Notes**: We have many caches. They are all documented. Some are persistent, and others are not.
The terminology is out of date with the paper, and uses "ornament" when it is really storing equivalences.

# 15

**Location**: [smartelim.ml](/plugin/src/automation/search/smartelim.ml).

**Notes**: File 3 uses this. It does not always produce the most efficient terms. It is meant to be easy to use.

# 16

**Location**: [ListToVect.v](/plugin/coq/examples/ListToVect.v).

**Notes**: This is a regression test for the DEVOID functionality, taken from DEVOID.
We are happy to note this explicitly in the paper if need be.

# 17

**Location**: [more_records.v](/plugin/coq/more_records.v).

**Notes**: These are just more complex versions of examples that the industrial proof engineer gave us,
only ones that do not rely on the industrial proof engineer's code.

# 18

**Location**: In a different zip file.

**Notes**: The industrial user is a non-author, and so I have not anonymized their repository.
I have attached the zip file for their repository seperately. I am legally obligated to distribute it with the license,
which gives away the company identity. Please do not check the license.
For an example using PUMPKIN Pi with the explained workflow on records to tuples, I recommend checking out the 
file `saw-core-coq/coq/handwritten/Lift/Lift/ConnectionLift.v`.
It is not documented extensively because it is not our code.

# 19

**Location**: [add_constr.v](/plugin/coq/playground/add_constr.v).

**Notes**: This starts by repeating work from file 1, then moves into the new work.
This is mostly a proof-of-concept, and I am pretty transparent both in the code and in the paper about the current limitations.
I have some exploratory work in step 4 of this file that is not discussed in the paper.

# 20

**Location**: [flip.v](/plugin/coq/playground/flip.v).

**Notes**: This is self-descriptive.

# 21

**Location**: [fin.v](/plugin/coq/playground/fin.v).

**Notes**: This example is in the table, but not discussed in the paper beyond that.
It is another example of changing inductive structure.
This is from the same external user as file 20.
This equivalence is used to express matrices with different representations with different tradeoffs.
One cute thing about this example is that the equivalence relies on functional extensionality in one direction,
so here we see where exactly that axiom shows up in the configuration!
And we can port nonaxiomatic code to axiomatic code, and likely (time constraints) similarly in the other direction.
It has functions and proofs, but not yet proofs that need propositional iota (time constraints).
The proofs of section and retraction are done using the algorithm from Section 4 even though there are much easier ways to prove them.
That is mostly to make a point.
We automate that for automatic configuration but not yet for manual configuration; this outlines how we could do it for manual as well.

# 22

**Location**: [ornerrors.ml](/plugin/src/lib/ornerrors.ml).

**Notes**: The name of this is not up-to-date with the paper, but it should give you an idea of what is going on.
The gist is that when either user errors or bugs cause CARROT to fail, most often Coq just gives us a type error.
This is useless to the proof engineer, who has no idea why CARROT was trying to define something with that type to begin with.
This is sort of analogous to the extraordinarily opaque error messages Coq gives when you use tactics that manipulate evars.
So to make this understandable to the proof engineer, every time the industrial proof engineer encountered a bug or user error,
we worked with them to determine why they were encountering that error.
We then included the reason in a list of common causes in the actual error message.
But we also included the scary-looking type error that Coq gave us, because sometimes it did include useful information.
We just disclaimed that with "Coq gave us this scary looking error."

So this is sort of like "eapply" saying
"we had inferred these constraints" and then telling you the constraints and some common reasons why this might happen,
rather than just telling you the constraints you had no idea it was inferring were wrong and leaving you to pray.
It's only a line in the paper but I think it's important engineering insight, maybe applicable to Coq more broadly, who knows.
It helped the proof engineer a lot.
But the infrastructure is a bit difficult to maintain.

