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
- `lang.v` - Syntax and instrumented small-step semantics of a
  programming language with incremental prophecy variables and IO
  specifications. Prophecy variable creation nondeterministically
  picks a stream of prophecy values; prophecy variable assignment
  loops if the assigned value does not match the first prophecy value
  of the stream, and otherwise replaces the stream by its tail in the
  prophecy heap.
- `lang_proph_erased.v` - An alternative small-step semantics for the same language,
  where the prophecy heap simply tracks the set of allocated prophecy variable
  identifiers. Creation does not branch; assignment does not loop.
- `proph_erasure.v` - Proves that if a program is safe under the
  prophecy instrumented semantics, then it is safe under after erasing
  prophecies.
- `rules.v` - Proves Hoare rules for the commands of the programming language
  against the instrumented semantics. These rules expose the prophecy variables
  as *constrained* incremental prophecy variables: an arbitrary (satisfiable)
  predicate on streams can be provided at prophecy variable creation time; the
  postcondition asserts that the prophecy value stream satisfies the predicate.
- `adequacy.v` Shows that proving a weakest precondition for the
  instrumented semantics (with both prophecies and IO specifications)
  implies safety of the fully erased program.
- `abstract_petrinet.v` Defines abstract Petri nets where places are
  Iris propositions.
- `coin.v` - Verifies the *coin toss* concurrent data structure.
- `buffered_io.v` Proves correctness of buffered output example.
- `channel.v` A simple in memory channel based on lists.
- `chat_server.v` A chat server example where the reading and writing
  over the network is abstracted.
- `chat_server_concrete.v` A concrete implementation of the chat
  server in `chat_server.v` which implements communication over the
  network as IO.
- `full_erasure.v` Erases the IO specifications from programs where
  prophecies are already erased.
- `lang_fully_erased.v` The programming language fully erased.
- `petrinet.v` Implements Petri nets in Iris.

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
