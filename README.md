# Quantified Class Constraints #

This repository provides a prototype implementation of type inference with translation to System F of Quantified Class Constraints, as presented in the paper ``Quantified Class Constraints'' by Gert-Jan Bottu, Georgios Karachalias, Tom Schrijvers, Bruno C. d. S. Oliveira and Philip Wadler.

**Tested with GHC 7.10.3 and GHC 8.0.2**

## Contents ##

The implementation is split over three directories: `Frontend`, `Backend` and `Utils`. The most important modules are the following:

  * Frontend
    + `HsTypes.hs`: Source language abstract syntax.
    + `HsParser.hs`: A simple parser.
    + `HsRenamer.hs`: The renamer.
    + `HsTypeChecker.hs`: The type inference algorithm with translation to System F, as explained in the paper.
    + `Conditions.hs`: The implementation of the `nonambig` condition, as explained in the paper.

  * Backend
    + `FcTypes.hs`: The abstract syntax of System F with datatypes and recursive let bindings.
    + `FcTypeChecker.hs`: A System F type checker.

## Building & Running ##

You can try out the prototype in two ways: build it as a cabal package and try the generated executable file or load it in GHCi.

### Try it in GHCi ###

The easiest way to try out the prototype in examples is by loading it in GHCi. For example:

    :load Main.hs
    runTest "Tests/Test2.hs"

### Build an executable ###

Since the implementation is also a cabal package you can also build an executable instead:

    cabal build
    ./dist/build/quantcs/quantcs Tests/Test2.hs

## Adding Tests ##

Apart from running the test files in directory `Tests`, you can also create and test your own. Currently, the prototype requires the syntactic restrictions explained in the paper. Additionally, we require the following:

* Type parameters of datatypes and type classes should be explicitly annotated with their kind.
* Type variables in instance heads should be annotated with their kind.
* Universally quantified variables should also be annotated with their kind at their binding site.

The above are illustrated in the existing tests in directory `Tests`. Since this is a proof-of-concept implementation, we do not perform kind inference, hence the above requirements (the implementation still performs kind *checking* though).

If you have any inquiries concerning the implementation please do not hesitate to [contact us](georgios.karachalias@cs.kuleuven.be).

