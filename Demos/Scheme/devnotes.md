# Development journal

## Sources

- William Clinger and Jonathan Rees, eds., [Revised⁴ Report on the Algorithmic Language Scheme](https://standards.scheme.org/official/r4rs.pdf) (1991).  The essential features, their arities, the formal semantics of §7.2, and the rewrite rules of §7.3 come from this PDF.  Section numbers in the code and documents refer to it.
- The user's design, kept with the session that prepared this work, gives the milestones, the acceptance cases, and the proof layers.  Its links pin leanexe at `4556fa8`, before the port to Lean v4.36.0.  This work follows the current tree and `AGENTS.md` where the two differ.

## Decisions

The user's decisions of 2026-11-27 limit the work to the design's milestones 1 and 2, with WebAssembly as the only target.  Exact integers use the fixnum profile, with the reference semantics over `Int` and the 61-bit range as a separate restriction predicate, so that a later bignum library replaces one numeric layer.  The heap reserves an object kind for integers of several words, and the bignum library `Library/Numerics/Bignum/`, which is not yet in this tree, will decide that kind's fields.  Adequacy against §7.2, the collector's proofs, and the space theorem are outside the request.

The stage-1 design was approved with these choices: the coverage of the reference semantics and the machine that [the inventory](inventory.md) marks *this request*, no non-essential extras, the export ABI `run mode cap outCap fuel src` with a status byte first, a typed outcome for every detectable error, and an attempt at a kernel-checked theorem that the export returns `(13 3)`.  The encoding of §7.2 waits for the user's choice between a defunctionalized transcription and a deep embedding of the report's metalanguage.  `Report.lean` comes last in the reference-semantics stage, and the work stops there for that choice if it has not arrived.

The report makes `if` with one arm, `=>` clauses, `let*`, `do`, named `let`, and `delay` non-essential, so the profile omits them, although the stage-1 design report had listed `let*`, `do`, and `=>` clauses among the forms to implement.  The rewrite rules of §7.3 for `cond` and `case` use only two-armed `if`, and the rule for `(cond)` asks for "some expression returning an unspecified value", which the core syntax supplies as a constant.

## Stage 3: the reference semantics

The reference semantics lives in `Demos/Scheme/Semantics/`: the data, the numeric layer, the reader, the core syntax, the expander, the machine, and the outcomes.  The machine is one total function `step` over configurations, with `Steps` as its iteration, so the rules are the function's clauses and a run reaches at most one final configuration (`final_unique`).  An inductive relation with one constructor for each rule would read the same and would need a proof of its agreement with an executable step for the derived results, and the function makes that agreement definitional.  Every definition recurses structurally or on a fuel, so the kernel evaluates runs: the `or` case takes 25 rules, repeated escape 136, and `letrec` re-entry 88, and `decide +kernel` checks the three results in about five seconds.

Three choices of representation came from Lean's checks.  `deriving DecidableEq` fails for a datum type with a `List Datum` field, a nested inductive type, so a vector holds its elements as a proper-list datum, and the type is an ordinary inductive type with derived equality, which the statements of the results need.  The expander first had a function `expandForm s rest` that `expand` called on the operands of a special form, and Lean rejected the structural recursion, because `expandForm` passed the same `rest` to `expandBody`, which is no smaller argument; the special forms now sit in `expand`'s own arm.  A recursive call on an `@`-pattern variable, as in `qq D a` after `.pair a@(.pair (.sym s) _) rest`, also failed: in the branch Lean replaces `a` by its pattern, which is no subterm.  Computing the call before the inner `match a` works, as `qq` does with `pairCore`.

A quoted constant must denote one object at every evaluation of its quotation, also when a continuation re-enters a top-level form, as the executable's reader allocates the program's text once.  `start` therefore expands every datum of the program before the run and allocates each compound literal of each expansion once, immutable, and the expansion refers to it by location.  A datum whose expansion fails keeps its syntax error, which the run reports when it reaches that form.  The expansion of a temporary needs no counter: each rule binds its temporaries around a body that names only them, or for `letrec` around the assignments, so a temporary of a fixed index per role is fresh in its region, and an inner rule that reuses an index encloses no reference to the outer one.

[The corpus](Corpus.lean) holds 104 programs with outcomes written by hand from the report and the profile, among them the capture cases of temporaries, of quasiquote's `cons`, and of `case`'s `memv`, the re-entry of a `map` callback and of a top-level form, and the range limits.  The reference semantics met every expected outcome on the first run.  `corpus_outcomes` checks the corpus in the kernel.  With 98 programs as one declaration its check took 38 s and peaked at 10.6 GiB, since the kernel keeps every reduction of a declaration until it ends, and in chunks of ten programs, one declaration each, it took 39 s and peaked at 2.8 GiB.  With 104 programs it takes 47 s and peaks at 3.0 GiB.

An independent review of the three results' statements found them about the reference rules, on the request's programs byte for byte, and not vacuous.  It ran variants of `step` against the statements and the corpus and found that no case told apart operands evaluated from right to left, an operator evaluated last, a `letrec` that assigns each variable as its initializer returns when the initializers run from right to left, an `or` that evaluates a test twice, and a `let` that reuses its location when a continuation re-enters it.  The cases `operand-order`, `operator-first`, `letrec-staging`, `or-once`, `and-once`, and `fresh-reentry` now tell each apart, and the reference semantics meets them.  The review also observed that §7.3's thunk rule for `or` places no source expression in the scope of its temporaries, so `or-42` rejects an expansion that binds `_` around the second test, not a wrong choice of the temporaries' names.

## Plan

- [x] Stage 1: design report.
- [x] Stage 2: [clause inventory](inventory.md) and [profile](profile.md).
- [x] Stage 3: reference semantics, the three derived results, and the corpus check.
- [ ] `Report.lean`, after the user's choice of encoding for §7.2.
- [ ] Stage 4: reader and expander in the dialect.
- [ ] Stage 5: evaluator and `call/cc`, after the closed-form bound is checked on a skeleton machine.
- [ ] Stage 6: export, call theorem with its allocation bound, and the compiled slice.
