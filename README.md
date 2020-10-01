# KU Leuven Haskell Compiler #

This repository contains the KU Leuven Haskell Compiler, a simple Haskell compiler featuring type inference with translation to System F.
The compiler is constructed at KU Leuven, under the programming languages group of [prof Tom Schrijvers](https://people.cs.kuleuven.be/~tom.schrijvers/), to serve as a basis for implementing and testing new compiler features.
This work is based on the following [prototype implementation](https://github.com/gkaracha/quantcs-impl).

**Tested with GHC 8.10.2**

## Implementation ##

The implementation is split over three directories: `Frontend`, `Backend` and `Utils`. The most important modules are the following:

  * Frontend
    + `HsTypes.hs`: Source language abstract syntax.
    + `HsParser.hs`: A simple parser.
    + `HsRenamer.hs`: The renamer.
    + `HsTypeChecker.hs`: The type inference algorithm with translation to System F.
    + `Conditions.hs`: The implementation of the `nonambig` condition.

  * Backend
    + `FcTypes.hs`: The abstract syntax of System F with datatypes and recursive let bindings.
    + `FcTypeChecker.hs`: A System F type checker.

## Building & Running ##

You can try out the compiler in two ways: build it as a cabal package and try the generated executable file or load it in GHCi.

### Try it in GHCi ###

The easiest way to try out the prototype in examples is by loading it in GHCi. For example:

    :load Main.hs
    runTest "Tests/Test1.hs"

### Build an executable ###

Since the implementation is also a cabal package you can also build an executable instead:

    cabal build
    ./dist/build/khc/khc Tests/Test1.hs
    
## TODOs ##

This is still an early version, so several improvements are planned for the near future:

* Include a System F evaluator, for executing programs.
* Write additional test files.
* Perform kind inference (the compiler currently only performs kind checking).

## Adding Tests ##

Apart from running the test files in directory `Tests`, you can also create and test your own. Currently, the compiler requires the following syntactic restrictions:

* Type parameters of datatypes and type classes should be explicitly annotated with their kind.
* Type variables in instance heads should be annotated with their kind.
* Universally quantified variables should also be annotated with their kind at their binding site.

The above are illustrated in the existing tests in directory `Tests`. We currently do not perform kind inference, hence the above requirements (the implementation still performs kind *checking* though).

If you have any inquiries concerning the implementation please do not hesitate to [contact us](mailto:gertjan.bottu@kuleuven.be).

