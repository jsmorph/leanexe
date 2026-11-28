# Development journal

## Sources

- William Clinger and Jonathan Rees, eds., [Revised⁴ Report on the Algorithmic Language Scheme](https://standards.scheme.org/official/r4rs.pdf) (1991).  The essential features, their arities, the formal semantics of §7.2, and the rewrite rules of §7.3 come from this PDF.  Section numbers in the code and documents refer to it.
- The user's design, kept with the session that prepared this work, gives the milestones, the acceptance cases, and the proof layers.  Its links pin leanexe at `4556fa8`, before the port to Lean v4.36.0.  This work follows the current tree and `AGENTS.md` where the two differ.

## Decisions

The user's decisions of 2026-11-27 limit the work to the design's milestones 1 and 2, with WebAssembly as the only target.  Exact integers use the fixnum profile, with the reference semantics over `Int` and the 61-bit range as a separate restriction predicate, so that a later bignum library replaces one numeric layer.  The heap reserves an object kind for integers of several words, and the bignum library `Library/Numerics/Bignum/`, which is not yet in this tree, will decide that kind's fields.  Adequacy against §7.2, the collector's proofs, and the space theorem are outside the request.

The stage-1 design was approved with these choices: the coverage of the reference semantics and the machine that [the inventory](inventory.md) marks *this request*, no non-essential extras, the export ABI `run mode cap outCap fuel src` with a status byte first, a typed outcome for every detectable error, and an attempt at a kernel-checked theorem that the export returns `(13 3)`.  The encoding of §7.2 waits for the user's choice between a defunctionalized transcription and a deep embedding of the report's metalanguage.  `Report.lean` comes last in the reference-semantics stage, and the work stops there for that choice if it has not arrived.

The report makes `if` with one arm, `=>` clauses, `let*`, `do`, named `let`, and `delay` non-essential, so the profile omits them.  The rewrite rules of §7.3 for `cond` and `case` use only two-armed `if`, and the rule for `(cond)` asks for "some expression returning an unspecified value", which the core syntax supplies as a constant.

## Plan

- [x] Stage 1: design report.
- [x] Stage 2: [clause inventory](inventory.md) and [profile](profile.md).
- [ ] Stage 3: reference semantics and the three derived results, then `Report.lean` after the user's choice.
- [ ] Stage 4: reader and expander in the dialect.
- [ ] Stage 5: evaluator and `call/cc`, after the closed-form bound is checked on a skeleton machine.
- [ ] Stage 6: export, call theorem with its allocation bound, and the compiled slice.
