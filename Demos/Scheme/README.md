# R4RS Scheme

This demo is an interpreter for the essential features of R4RS Scheme, with a reference semantics in ordinary Lean and an executable reader, expander, and evaluator in the verified compiler's dialect.  The work follows the milestones of a design that a user supplied, and this tree holds its first, the source contract, and the reader, expander, and evaluator of its second.  [The clause inventory](inventory.md) lists every essential form and procedure with its status, [the profile](profile.md) states the choices that the report leaves to an implementation, and [the journal](devnotes.md) records the decisions and the stages.

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

## The transcription of §7.2

`Demos/Scheme/Report.lean` transcribes the formal semantics of §7.2, printed pages 34 to 36.  Lean admits only strictly positive inductive types, and E occurs to the left of the arrows of F = L × (E* → K → C), so each λ-abstraction of the equations whose value is a procedure's function, an expression or command continuation, or an argument of `single` or `tievals` is a constructor of a code type whose fields are its free variables, and each equation is one clause of `Demos.Scheme.Report.step`, which cites its equation and page.  The module's docstring lists each rule that the report leaves to the implementation, to prose, or to nothing, with its clause, among them `K`, `new`, `wrong`, `permute`, the answers, the initial environment, `cdr`, and the elided clauses of `eqv`.  `Demos/Scheme/ReportCheck.lean` computes the three programs through the transcription, under the reference reader and expander, as a cross-check of the reference semantics, not a proof of adequacy.

| Theorem | Statement |
|---|---|
| `Demos.Scheme.ReportCheck.report_or_case`, `report_repeated_escape`, `report_letrec_reentry` | The equations of §7.2 give the three programs the answers 42, `(13 3)`, and `(10 1)`. |
| `Demos.Scheme.ReportCheck.cross_check` | On the three programs, the transcription's answer is the reference semantics's result. |
| `Demos.Scheme.ReportCheck.cross_check_more` | The same for nine programs that reach rest lists, `apply`, `car`, `cdr`, `set-car!`, `eqv?`, an escape through `apply`, and the translation of definitions. |
| `Demos.Scheme.Report.new_unallocated` | The allocator meets the axiom of p. 34: `new σ` is not in use in `σ`. |

## The executable interpreter

The modules of `Demos/Scheme/Machine/` hold the interpreter in the verified compiler's dialect: one record with an arena of five-word slots and an output buffer, and a step function that dispatches on the phase.  The reader reads one token at each step, the expander follows the reference expander function by function, and the evaluator follows the reference machine's rules over code, chains of cells, and frames, each with its pending work in frames of the arena.  A continuation is a chain of frames that no rule changes, so an escape procedure resumes the same work as often as it is called.  `Demos.Scheme.Machine.runWith names mode cap outCap fuel src` runs at most `fuel` steps and returns a status byte and text: in mode 0 the data of the program, in mode 1 the code of its forms in a tagged form, and in mode 2 the value of its last form.  The case executable `verified-cases-scheme` of `tests/TestSupport/Scheme/CasesMain.lean` compares the three modes with the reference semantics on the corpus and 66 programs of syntax, compares mode 2 with the outcomes that the corpus states by hand, checks the outcomes of an exhausted fuel, a full arena, and a full output buffer, and fails at a difference.

