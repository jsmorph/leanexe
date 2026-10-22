# Checked outward rounding

[The native operations](Program.lean) return `Checked`, with status zero for an accepted finite
endpoint and status one for rejection.  `endpoint` moves a rounded binary64 result one adjacent
word upward or downward and rejects nonfinite results or endpoints.  `outAdd`, `outSub`, `outMul`,
`outDiv`, and `outSqrt` also check their inputs.  Division rejects a zero denominator.

[The mathematical proofs](Proof.lean) connect accepted endpoints to the word-level outward-rounding
theory in `LeanExe.ProofKit.F64OutwardAccepted` and prove the corresponding real inequalities.
Their named premises state the accepted domains.  [The compiled module](Compiled.lean) supplies
execution proofs, with [a flat encoding](Encoding.lean) of status and value.

The exported bit helpers preserve their word-level definitions.  `nextUpBits` and `nextDownBits`
require suitable finite input words when interpreted as adjacent real values.  The checked
operations enforce those conditions before accepting a result.
