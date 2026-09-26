# Id-annotated propositional comparisons

Candidate `c8b59c3abbc7e8017f42892b70faa7c581df46ae` extends `compile-arithmetic` with finite Id type
annotations on the UInt64 argument of `=`, `≠`, `<`, `≤`, `>` and `≥`.
The source syntax retains the annotations. The extractor requires the standard
order instances and exact decision evidence. The shared lowering and WASM
admission proofs cover every accepted annotation depth.

Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0, and authorized serial local
execution through `tools/leanrun`:

- `tools/arithmetic-check.js proof`: all nine compiler axiom audits pass,
  including exact module decoding, validation, and terminating exported execution
  with the source result in the pinned WASM model.
- `tools/arithmetic-check.js subset-engine id-comparison`: 597 native Lean/V8
  comparisons across 35 declarations, including twelve range declarations.
- `test/scalar_id_comparison.lean`: 240 native/IR comparisons across fifteen
  declarations, plus five rejected declarations.
- `test/scalar_comparison_id_type.lean`: 252 native/IR comparisons across all six
  comparison forms and three annotation patterns, plus 210 rejected type,
  universe, instance, and decision inputs.
- The preceding negative-condition, Id-arithmetic, and primitive-Id fixtures
  pass unchanged: 198, 208, and 840 comparisons, with 4 and 300 rejection cases
  in the latter two fixtures.

Twenty selected prior WASM modules match the ciogpt integration binaries byte
for byte. The full native fixture contains 675 declarations; the emitted-WASM
check here covers the selected 35. The native, admission, and focused test
bodies match for all fifteen new accepted declarations. The independent core
type-safety implementation, runtime, and binary serializer are unchanged.

The condition and decision procedure must contain identical operand expressions.
Six original scalar probes compile unchanged. The original loop probe remains
rejected because expected types put different annotations inside its condition
operands and decision operands. It is preserved as
`rangeIdComparisonEvidenceAnnotations`; the accepted loop variant uses explicit
UInt64 operand annotations. Supporting those differing operand expressions
requires a further source-equivalence proof and is the next increment.

The initial ordinary-if draft fails Lean decision-instance synthesis and is
retained separately. The first valid fixture and its rejected loop case are also
retained. This directory includes the accepted binaries, hashes, exact test
sources, compiler proof log, engine results, and focused test logs.
