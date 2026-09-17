# Experimental WGSL backend

The [development plan](../../WGSL.md) targets independently verified Wasm/WGSL
bundles. This directory records implementation progress, not a completed GPU
correctness claim.

## Checked foundation

- `LeanExe.WGSL.Profile` separates scalar policies from source-ordered expression
  evaluation and multiply-add fusion. Lean proves reflexive/transitive profile
  refinement, expression-execution inclusion, transfer of universal output
  properties, and existence given a total scalar interpretation.
- `LeanExe.WGSL.Obligations` makes successful execution, nontermination, dynamic
  errors, computation correspondence, numerical bounds, and exactness distinct.
  Its composition lemmas require a total execution theorem; they do not establish
  that a WGSL kernel satisfies those obligations.
- `LeanExe.WGSL.Generate` emits an untiled row-major FP32 GEMM. A typed
  `KernelCandidate` marks a checked Lean GEMM definition for this narrow lowering.
  This is a first source mechanism, not arbitrary Lean program extraction.
  Each invocation owns one output; partial workgroups exit before accessing
  buffers. Validation bounds dimensions, storage sizes, binding identities,
  workgroup size, and dispatch counts.

The scalar semantics in the root library are currently parameters. Neither a
concrete binary32 interpretation nor artifact execution correctness follows from
these parametric lemmas. Config validation is a generation check, not yet an
indexing, race-freedom, or termination theorem.

## Profiles and trust boundary

The pinned source is [WGSL, 17 August 2026, §15.7](https://www.w3.org/TR/2026/CRD-WGSL-20260817/#floating-point-evaluation).
WGSL allows implementation latitude in rounding, subnormals, signed zero, fusion,
and reassociation. V1 assumes source order and supports two candidate restricted
profiles, both at revision 1:

| ID | Arithmetic | Multiply-add |
|---|---|---|
| `leanexe-f32-rne-separate-v1` | Nearest/even, preserve subnormals, IEEE zero signs | Separate |
| `leanexe-f32-rne-fusion-v1` | Same scalar choices | Separate or fused locally |

Both profile records select IEEE exceptional handling; planned GEMM numerical
theorems must show that exceptional cases are unreachable on their advertised
domains. Runtime conformance to either profile is an explicit assumption.
Shader text alone cannot force these restrictions. Runtime observations are
evidence for individual executions, not universal conformance proofs.

## Verification

All Lean commands use the repository runner and its shared machine-wide lock.

```sh
tools/leanrun --timeout 3m lake build LeanExe.WGSL.Profile LeanExe.WGSL.Obligations LeanExe.WGSL.GenerateTest
```

If using a repository-local toolchain, pass `--toolchain` to the runner or set
`LEANRUN_TOOLCHAIN` for a driver. The pinned toolchain is Lean 4.34.0-rc2.

## Remaining gates

The [native harness](../../tools/wgsl/README.md) now executes captured artifacts
and retains exact source/profile/configuration evidence. The first rectangular
kernel passed on Mesa llvmpipe; failure probes are preserved under
`test/wgsl/evidence`. These observations do not establish runtime conformance.

1. Expand the fixed execution corpus beyond the first rectangular artifact.
2. Parse the actual WGSL text in Lean; validate the emitted subset independently
   of the generator and manifest.
3. Instantiate shared operational semantics and binary32 arithmetic; prove
   indexing, unique writes, successful termination, and execution correspondence.
4. Prove GEMM numerical bounds and restricted exactness, then independently check
   the exact artifact package.
5. Add the Wasm dispatch boundary, bundle composition, and mixed-precision GPT-2
   integration before doing residency, tiling, and performance work.

The existing pinned Talos dependency has pure binary32 operations and numerical
lemmas. Reuse belongs in the existing proof workspace, preserving its dependency
and license boundary rather than copying third-party source into the compiler.
