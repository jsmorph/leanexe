# Local helpers around Boolean-to-word loops

The previous increment passed all nineteen proof audits and 609 native/WASM comparisons. This increment reuses the independently defined helper semantics and pure helper-body compiler already used by Boolean-result loops. Helpers remain pure; their captures are checked against every fresh loop store. Multiple sequential or nested loops and full-dialect correctness remain open.

The source evaluation rules and totality proof passed immediately. I selected the simpler pure helper paths from the word-loop extractor rather than the newer Boolean loop-call continuations: loop-containing helper bodies are outside this increment. Matching Id input/domain pairs normalize recursively as in the Boolean-result path.

Two scratch generation attempts used an incorrect end marker for the Id normalization case and stopped before changing the extractor. The first extraction checks then exposed proof equation differences: rewriting the direct match closes several do-bind equalities automatically, while the generic scalar let cases need explicit equations to discharge the newly preceding function-pattern exclusions. The failed logs are retained. No unchanged timed-out command was rerun.

Acceptance now uses specialized scalar-let equations to prove the function-pattern exclusions once. The direct helper extraction proofs reuse the existing pure closure arguments; source totality, acceptance, recovery, correctness and invariants pass. Removed unused simplifier arguments introduced by the adaptation.

The PUnit native example initially left its universe unspecified. The fixture and its registered copies now use PUnit.{1}, matching the accepted standard syntax. The failed source and log are preserved. All ten native declarations pass 240 comparisons. Five syntax families pass 209,664 comparisons, 112,896 invalid-input tests and 14,976 controls, covering public/direct plan equality and unused helpers. Inputs include both argument orders, overflow values, all binder kinds, lexical captures, nested helper declarations, zero/two Id input layers, and zero/two result layers. Helper bodies are checked even when unused.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1337 declarations.
