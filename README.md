## Dependencies

The only dependency to use the plugin is Coq 8.8.

To run the case study code, you also need the following:
* The [univalent parametricity framework](https://github.com/CoqHott/univalent_parametricity)
* [Datamash](https://www.gnu.org/software/datamash/)

## Building

### Plugin

```
coq_makefile -f _CoqProject -o Makefile
make && make install
```

### Case Study Dependencies

Run the following to make the Univalent Parametricity framework:

```
cd <path-to-univalent-parametricity>
make && make install
```

Datamash should install in a straightforward way from a package manager using the link above.

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

There are two ways to run the case study, in two different scripts.
The reason for the two different versions is that the univalent parametricity framework (hereon UP) has different
Coq dependencies, so the base functions perform differently. 
The first way uses the same exact input datatypes for both DEVOID and UP,
copying and pasting in the functions DEVOID produces to run on the dependencies of UP;
This is the version that the paper uses, as the results it produces are the easiest to understand.
The second way does all of the lifting from scratch with
the base datatypes in both the DEVOID code and UP;
these results are more difficult to interpret, and is not the version in the paper.

Each of these scripts takes a while, as it runs each function ten times each
on large data both for DEVOID and for UP.

#### Reproducing the Paper Case Study

Enter the `eval` directory:

``
cd eval
``

Run the following script:

```
./TODO.sh
```

Then check the `together` folder for the median runtimes (Figures 13 and 15) as well as the size of reduced functions.
This also does a sanity check to make sure both versions of the code produce the same output.
It does not yet try to reduce the proof that timed out with UP after an hour (it reduces it with DEVOID, but not with UP),
otherwise the case study would take ten hours to run. To run this just once, enter the `equiv4free` directory:

``
cd equiv4free
``

In that directory, uncomment the following line in `main.v`:

```
(*Redirect "../out/normalized/prepermutesin-sizedUP" Eval compute in pre_permutes'.*)
```

Then run the following script, which runs the UP code just once with a timeout:

```
./prepermutes.sh
```

The timeout is an hour, so grab a coffee or read a book or something. It should timeout,
or finish normalizing very close to the timeout limit (if so, the script will record how long it took).

#### Using Different Datatypes

This is not in the paper, but you might be curious for the sake of validity whether the same benefits apply
lifting the datatypes separately from scratch. To see that they do, run the second version, run the following script:

```
./separate.sh
```

Then check the `separate` folder for the results.







