# iris-io

Verifies with
- [Coq 8.7.2](https://github.com/coq/coq/releases/download/V8.7.2/coq-8.7.2-installer-windows-x86_64.exe)
- [Coq-std++](https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp/commit/aa942ca85603ae4e88a963abc7691e77ed3c46a7)
- [Ssreflect](https://github.com/math-comp/math-comp/archive/mathcomp-1.6.4.zip)
- [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/commit/1d29427d2532d1873f94d158bce72f18a7912f55)
- [Autosubst](https://github.com/uds-psl/autosubst/commit/d0d73557979796b3d4be7aac72135581c33f26f7)

To verify, just type `make`.

## Structure

- `prelude/base.v` - Streams
- `lang.v` - Syntax and instrumented small-step semantics of a programming
  language with incremental prophecy variables. Prophecy variable creation
  nondeterministically picks a stream of prophecy values; prophecy variable
  assignment loops if the assigned value does not match the first prophecy
  value of the stream, and otherwise replaces the stream by its tail in the
  prophecy heap.
- `lang_erased.v` - An alternative small-step semantics for the same language,
  where the prophecy heap simply tracks the set of allocated prophecy variable
  identifiers. Creation does not branch; assignment does not loop.
- `erasure.v` - Proves that if a program is safe under the instrumented
  semantics, then it is safe under the erased semantics.
- `rules.v` - Proves Hoare rules for the commands of the programming language
  against the instrumented semantics. These rules expose the prophecy variables
  as *constrained* incremental prophecy variables: an arbitrary (satisfiable)
  predicate on streams can be provided at prophecy variable creation time; the
  postcondition asserts that the prophecy value stream satisfies the predicate.
- `coin.v` - Verifies the *coin toss* concurrent data structure.

## Axioms used

Note that axioms below reported by coqchk starting with "iris." are
not axioms; coqchk gets confused by the module system of Coq.

```
$ coqchk -o -R . iris_io -silent -admit stdpp.pretty iris_io.erasure iris_io.coin

CONTEXT SUMMARY
===============

* Theory: Set is predicative

* Axioms:
    Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
    Coq.Logic.PropExtensionality.propositional_extensionality
    Coq.Logic.Classical_Prop.classic
    iris.base_logic.lib.iprop.iProp_solution.iPreProp
    iris.base_logic.lib.iprop.iProp_solution.iProp_fold
    iris.base_logic.lib.iprop.iProp_solution.iProp_fold_unfold
    iris.base_logic.lib.iprop.iProp_solution.iProp_unfold
    iris.base_logic.lib.iprop.iProp_solution.iProp_unfold_fold
```
