# Boolean loop accumulators

The six fixed native probes all reject before changes. Elaborated toggle and
break bodies retain Boolean lets, standard Id pure and ForInStep Bool branches.
The Boolean iteration encoding and native stride proof pass on their first run.
The first source step module failed on ambiguous implicit flag types in dot
notation and field names that shadowed the branch expressions. Explicit
Bool.toUInt64 applications and distinct proof-field names correct both issues.
The corrected source step grammar and its totality theorem pass (65 targets).
Original source/log failures are retained. No public compiler behavior changes
until step/range extraction and all proofs are connected.

The step extractor correctness proof needed explicit Option.map syntax in the
result-annotation parser, an unfold for metadata, and the actual constructor
binder order for conditional evaluation. Acceptance, support and invariant
proofs then pass together (145 targets). A checked induction diagnostic records
the nine generated cases.

The range syntax/parser accepts exactly the standard Bool accumulator head and
preserves checked Nat index annotations, bounds and positive strides. Source
semantics needed fully qualified Count relations and their Nat results rather
than UInt64 projections. The corrected source and parser pass. The range
extractor first failed on structure-literal indentation, then an implicit plan
witness in acceptance. Its correctness proof needed an explicit UInt64 type for
the decoded word accumulator; otherwise numeral defaulting inferred Nat. The
complete range extraction, acceptance, support, invariants and correctness now
pass (178 targets). No timeouts occurred. Public integration remains next.

Public integration initially left reduction obligations for the canonical range
head and wrapper fallback. A separate definitionally checked no-wrapper fact
and explicit simplification of the head discharge those obligations. Source
acceptance/support pass (185 targets), then public correctness and invariants
pass (188 targets), followed by the public extractor (203 targets).

All six fixed accumulator probes now pass unchanged. All fifteen earlier
outer-helper probes pass: three restored accumulators and twelve retained
positive controls. The new syntax corpus passes 13,824 native comparisons and
6,912 invalid-input tests on its first run. The twelve native tests first
needed an explicit Nat annotation on their diagnostic counter, then all 288
comparisons pass. Public Boolean inputs include high-bit and all-ones ABI
values; range cases include empty ranges, early exits and large strides.

The general source-to-WASM theorem and nineteen audits pass (3384 targets). Two additional audits check native Boolean iteration and its word encoding. Passed 1101 native Lean / independent Wasm engine comparisons across 56 declarations.
44 prior modules retain identical bytes; 0 changed. Prior tests pass 47856 comparisons, 25488 invalid-input checks and 0 controls.
