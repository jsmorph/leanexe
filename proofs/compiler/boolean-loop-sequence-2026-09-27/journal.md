# Word prefixes with Boolean-result loop continuations

All six fixed probes reject before this increment. The baseline probe initially
used a nonexistent UInt64.beq constant; ordinary equality fixes that test driver.
The corrected baseline and initial failure are retained.

BooleanSequence has its own source evaluation and support predicates. Word
prefixes reuse the checked word-sequence grammar. Boolean-result leaves, ordinary
word lets, exact standard Id binds, run/pure and metadata are checked independently
of extraction. Source totality, extraction, complete admission and source
reconstruction pass first try (207 targets). Capture preservation, correctness
and bounded IR invariants pass first try (212 targets).

The existing sequence plan, descriptors, execution, function bytes and stack
validation work unchanged. Public compilation preserves the existing admission
paths before the Boolean-sequence fallback. Source application and Boolean result
encoding pass with descriptor admission (244 targets). WASM execution passes on the first integration check; the function-byte branch needed
its explicit flag.toUInt64 witness in place of the word-value name copied during
adaptation. The corrected focused byte target passes 3360 targets.

All six unchanged probes now compile. Eight native fixtures pass 192 comparisons
on their first run. The syntax matrix's first check catches the reserved Lean
token prefix used as a local variable; renaming it to nextWord corrects the test.

The corrected syntax matrix passes 13,824 comparisons, 18,432 invalid-input
checks and 576 admission controls. Combined with native fixtures this gives
14,016 comparisons. The matrix checks word prefixes with Boolean continuations,
including a two-loop word prefix, dependent bounds, early exits, continue,
retained Id annotations, wrappers and zero-count malformed computations.
Four additional proof boundaries are audited. The engine group retains all 124
prior declarations and adds eight Boolean-sequence fixtures.

The complete source-to-WASM gate passes 3418 targets and all 57 audits. Passed 2795 native Lean / independent Wasm engine comparisons across 132 declarations.
All 124 prior modules retain identical bytes. All six fixed Boolean-result probes compile. Prior tests pass 23,424 comparisons, 36,096 invalid-input checks and 960 controls. All six next Boolean-prefix probes reject before the next increment.
