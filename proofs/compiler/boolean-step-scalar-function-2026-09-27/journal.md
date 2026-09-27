# Scalar helper declarations within Boolean steps

Four fixed word/Boolean input/output probes reject before changes. The new
source rules reuse existing scalar closure kinds and scalar body semantics.
Exact Id input/domain/output annotations are checked. Source totality passes
66 targets after correcting the implicit binder order in the two Boolean-output
cases. No new source value representation is needed.

A checked induction diagnostic identifies 25 extractor cases. Extraction
correctness and acceptance pass on the first attempt. Support and invariant
proofs need the attached local lists introduced by functional induction normalized
with List.attach_map_val. The support proof also needs scalar kind projection
normalized before unfolding the scalar kind function, followed by the same list
map normalization in the goal. These adjustments pass 147 targets. Unused simp
arguments are removed; a scratch edit script initially used the wrong diagnostic
column offset, and its failed invocation and unchanged build log are retained.
There were no timeouts or new proof assumptions. The public target passes
205 jobs. Four fixed probes now compile. Twelve native declarations pass 288
comparisons; generated syntax tests pass 27,648 comparisons and 16,128 invalid
inputs, including unused invalid bodies in empty ranges. Both tests pass on their
first runs. This extension reuses existing scalar and WASM representations.

The general source-to-WASM theorem and nineteen audits pass (3386 targets). Passed 1101 native Lean / independent Wasm engine comparisons across 56 declarations.
44 prior modules retain identical bytes; 0 changed. Prior tests pass 81840 comparisons and 43296 invalid-input checks. Four fixed step-match probes remain rejected for the next capability.
