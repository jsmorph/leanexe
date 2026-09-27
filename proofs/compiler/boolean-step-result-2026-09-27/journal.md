# Complete Boolean step-result bindings

Before changes, the saved, ignored-done and conditional-binding probes reject;
the simple monadic bound probe already compiles. The prior retained/show helper
probe is also fixed and rejected. New source and compiled result kinds keep
both value and exit status and project to Unit in scalar contexts. Their
lookup/matching/projection proofs pass first try (20 targets). Source rules for
result variables, ordinary lets and standard Id binds have a totality proof
(66 targets). A checked diagnostic records nineteen extractor cases. Exact
annotation parsing, acceptance/support, correctness and invariant proofs all
pass on their first combined run (147 targets). Existing function signatures
and scalar bindings retain their previous rules.

Public extraction passes (205 targets). Saved and ignored-done probes now
compile, and the unchanged retained/show helper probe is restored. The bound
probe and three existing helper probes remain accepted. The conditional
step-result bind still needs a local function taking a complete step result;
its source is preserved for the next capability. The ten native programs pass
240 comparisons, and the syntax corpus passes 18,432 comparisons and 9,600
invalid-input checks. All these tests pass on their first runs.

The general source-to-WASM theorem and nineteen audits pass (3386 targets). Passed 1053 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. Prior tests pass 65472 comparisons and 39456 invalid-input checks. Six fixed accumulator probes remain accepted.
