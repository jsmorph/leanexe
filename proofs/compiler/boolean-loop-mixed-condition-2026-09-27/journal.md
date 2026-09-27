# Mixed scalar and loop arms in Boolean conditions

An outer Boolean condition can now select a scalar Boolean result or a loop in
either arm. Both-scalar arms use the same checked interface. Each arm first tries
scalar extraction; a thunk runs loop extraction only if scalar extraction fails.
Both arms are checked even when the condition is constant.

A scalar arm has a zero-iteration plan with zero count, initial, step and exit
fields and its compiled Boolean result. The new scalar-plan lemma proves its
meaning without a loop step. The existing captured-condition lemma selects
between scalar and loop plans unchanged. Source evaluation distinguishes a
selected scalar arm from a selected loop arm, and support checks cover all four
arm combinations. No WASM lowering change is needed.

The first proof attempt needed explicit scalar/fallback arguments in the arm
acceptance helper; leaving them implicit did not give simplification enough
information. Functional induction omits the unused Unit thunk argument, so the
IHs remain direct. The next attempt corrected equalities already substituted by
case analysis. Source totality, extraction acceptance/soundness, arm/plan
correctness, invariants, public extraction and WASM admission then pass. Unused
simp arguments introduced in the helper are removed.

Ten native declarations pass 240 comparisons across both arm orders, constants,
comparisons, public flags, nested conditions, captured helpers, break/continue,
stride and Id results. Raw syntax tests pass 96,768 native/IR comparisons:
48,384 through the public function extractor and 48,384 through the range
extractor directly, including both-scalar arms. They also pass 41,472 invalid-input
checks and 3,456 wrapper controls. The initial raw fixture incorrectly requested
BooleanComparison.lt, which does not exist; its scalar comparison now uses a
supported modular equality. The failed file and log are retained. Conditions
still cover all eight word comparison forms, Boolean flags/negations and constants.
Invalid checks include bad scalar and loop arms, unused branches, decision
evidence, output annotations and conditional heads/universes.

Selected preceding outer-condition, Unit-helper and multiple-argument tests are
rerun. The complete compiler proof and native Lean/V8 checks follow this candidate.
Conditional do continuations containing loops, broader helper/proposition bodies,
general loop composition and full-dialect compiler correctness remain open.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1236 declarations.
