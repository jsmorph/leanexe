# R4RS Scheme

This demo is an interpreter for the essential features of R4RS Scheme, with a reference semantics in ordinary Lean and an executable reader, expander, and evaluator in the verified compiler's dialect.  The work follows the milestones of a design that a user supplied, and this tree holds its first: the source contract.  [The clause inventory](inventory.md) lists every essential form and procedure with its status, [the profile](profile.md) states the choices that the report leaves to an implementation, and [the journal](devnotes.md) records the decisions and the stages.

## The reference semantics

The modules of `Demos/Scheme/Semantics/` define the meaning of a program's bytes under the profile.  The reader of `Read.lean` gives the data of §7.1.2, and the expander of `Expand.lean` rewrites each datum into the abstract syntax of §7.2.1 by the rules of §7.3 and the quasiquotation rules of §4.2.6 and §7.1.4.  The machine of `Machine.lean` is one step function over configurations of an expression, an environment, a list of frames, and a store, whose values follow the domains of §7.2.2.  `Numeric.lean` computes every numeric procedure over `Int`, and the profile's restriction to the 61-bit range is the separate predicate `Demos.Scheme.Semantics.Numeric.fixnum`.  `Outcome.lean` gives the bytes of an outcome, a status byte and a text, which the executable interpreter will write for the same program.

| Theorem | Statement |
|---|---|
| `Demos.Scheme.Semantics.Results.or_case` | The rules lead `(let ((_ 42)) (or #f _))` to the value 42, and every final configuration they reach from it is that value. |
| `Demos.Scheme.Semantics.Results.repeated_escape` | The same for the repeated-escape program of the design and the list `(13 3)`. |
| `Demos.Scheme.Semantics.Results.letrec_reentry` | The same for the `letrec` re-entry program and the list `(10 1)`. |
| `Demos.Scheme.Semantics.Results.outcomes` | The bytes of the three outcomes are status 0 followed by `42`, `(13 3)`, and `(10 1)`. |
| `Demos.Scheme.Semantics.CorpusCheck.corpus_outcomes` | The reference semantics gives each program of [the corpus](Corpus.lean) the outcome that the corpus states by hand. |
| `Demos.Scheme.Semantics.final_unique` | A run reaches at most one final configuration. |

The kernel evaluates each run, and the theorems depend on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  `lake build Demos.Scheme.Semantics.Results Demos.Scheme.Semantics.CorpusCheck` builds and checks them in about 55 s, with a peak of 3.0 GiB for the corpus.
