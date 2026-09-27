# Inspecting complete Boolean step results

All four unchanged probes reject initially. A separate checked shape diagnostic
shows explicit casesOn uses the standard primitive, while ordinary match calls
a generated matcher declaration. This increment covers primitive nondependent
casesOn. Generated declarations require a separate checked expansion capability.

The source rules evaluate the complete input, bind its Boolean payload and run
only the selected branch. Support checks both branches, the canonical Boolean
parameter/motive/branch domains and the nondependent result annotation, including
standard Id result layers. Source totality passes 66 targets on the first try.
The checked extractor induction has 26 cases. All extraction correctness,
acceptance/support and invariant proofs pass first try (147 targets); the public
compiler target passes 205 targets. No new assumptions or timeouts occurred.

The fixed direct, captured-helper and retained-Id probes now compile. Ordinary
match remains rejected with its original source preserved. Eight native programs
pass 192 comparisons. Generated syntax tests pass 18,432 comparisons and 10,752
invalid-input checks. They distinguish returning from inspecting a done result,
exercise nested inspection and payload captures, and reject unused invalid
branches even in an empty range. Both tests pass on their first runs.

The general source-to-WASM theorem and nineteen audits pass (3386 targets). Passed 1005 native Lean / independent Wasm engine comparisons across 52 declarations.
44 prior modules retain identical bytes; 0 changed. Prior tests pass 95760 comparisons and 51936 invalid-input checks. The ordinary-match probe remains rejected because it uses a generated declaration; three explicit casesOn probes compile.
