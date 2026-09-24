# Certified scalar64 acceptance corpus

Five portable packages bind the actual Lean source declarations to exact WASM
bytes through the generic scalar backend and independent binary validator.
They are separate from the ordinary compiler's source-driven and artifact
registries. No pilot supplies an instruction-by-instruction WASM proof.

The source/proof/tool revision is
`e4bb6d08670e6fa6495e0cc32efa4e84ee2e95fc`. Each package records it, the exact
Lean and dependency pins, source and certificate names, core/IR, ABI, export,
file hashes, and canonical checking declarations.

| Package | Original source | Bytes |
|---|---|---:|
| [affine](packages/affine) | `LeanExe.Examples.Arithmetic.affine` | 53 |
| [choose](packages/choose) | `LeanExe.Examples.Arithmetic.choose` | 58 |
| [mix](packages/mix) | `LeanExe.Examples.Prng.mix` | 89 |
| [helper](packages/helper) | `LeanExe.Examples.ScalarHelper.caller` | 78 |
| [gcd](packages/gcd) | `LeanExe.Examples.TalosGcd.gcd` | 90 |

From the repository root:

```sh
tools/verify-certified proofs/talos/scalar64/packages/gcd
tools/check-correct --packages proofs/talos/scalar64/packages --verify-only --mutations --cold
```

The second command verifies existing packages without compiling them, runs
boundary and engine checks, audits declarations, rejects altered packages, and
verifies the five packages again in a detached checkout with no project proof
cache. Only pinned external dependency caches are shared. The runner's normal
resource policy applies; explicitly authorized local execution can use
`LEANRUN_LOCAL=1`.

[The correctness guide](../../../docs/scalar64-correctness.md) states the proof
boundary, numeric semantics, certificate extension procedure, and assumptions.
[The task journal](../../../task.md) records completed checks and failures during
development. `acceptance.json` records the final gate results and artifact hashes.

The final gate passed on 2026-09-24: five independently verified packages, five
clean-checkout verifications, 333 engine cases, 15 mutation rejections, and the
source/admission and axiom audits. The audit checked 494 scalar declarations and
2,181 independent TypeSafety declarations under their documented axiom policies.
