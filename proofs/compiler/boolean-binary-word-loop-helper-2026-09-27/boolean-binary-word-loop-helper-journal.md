# Binary Boolean helper declarations around word-result loops

All six fixed native probes reject before the extension, including after the
Unit-prefixed Boolean-step increment. The new WordRange source rule reuses the
existing scalar binary predicate kind and exact helper syntax. Source evaluation
and totality pass 84 targets on the first attempt.

Extraction retains the three existing scalar/range/Boolean-derived-word paths.
Only after those reject does a two-word helper with no word result or many-word
signature try binary Boolean recognition. Its body is checked with two word
placeholders and the continuation is compiled under the captured closure. The
exact equation is conditional on the three earlier paths rejecting. Termination
and the equation pass on the first isolated attempt; the induction has 33 cases.

Complete admission, source reconstruction, correctness across all loop stores
and both IR projection invariants pass 201 targets on the first combined attempt.
Three unnecessary attach-map simplifications are removed; this extractor's
induction closure does not contain an attached environment. Function integration,
focused tests and complete WASM/engine checks remain.

Function integration passes 211 targets and all six fixed probes compile. Eight
native fixtures pass 192 comparisons. The syntax test initially needs an explicit
UInt64 annotation on the native forIn result for overloaded addition; that
test-only correction leaves source expressions unchanged. The matrix then passes
9,216 comparisons, 17,664 invalid-input checks and 384 controls. It covers ordinary
and retained Id results, independent binder annotations, wrappers, both junctions,
unused helpers, calls in bounds and initial values, and calls after the loop.
Every malformed case is also checked with an empty range. The 106-declaration V8
group retains all 98 prior declarations and adds eight word-loop fixtures.
