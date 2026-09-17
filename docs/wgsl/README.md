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

The scalar semantics in the root library are parameters. The
invocation model now establishes successful termination, dynamic-error absence
and source-ordered dot-product correspondence under scalar totality and buffer
size preconditions. The dispatch layer lifts this result to arbitrary
interleavings and observable matrix outputs. `Project.WGSL.Binary32` in the
existing Talos proof workspace supplies a concrete interpretation and restricted
exactness for the captured rectangular shader. `ArtifactNumerical` composes the
dispatch theorem with a binary32 accumulation bound.

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

1. Expand the fixed native execution corpus beyond the first rectangular artifact.
2. Independently check the exact artifact package with the concrete binary32
   interpretation, numerical bound and restricted exactness now proved.
3. Add the Wasm dispatch boundary, bundle composition, and mixed-precision GPT-2
   integration before doing residency, tiling, and performance work.

The existing pinned Talos dependency has pure binary32 operations and numerical
lemmas. Reuse belongs in the existing proof workspace, preserving its dependency
and license boundary rather than copying third-party source into the compiler.

## Concrete binary32 checkpoint

`proofs/talos/lean/Project/WGSL` reuses Talos addition, multiplication and dyadic
rounding, adds a single-rounding fused multiply-add, and checks eleven arithmetic
edge cases by kernel reduction. The public theorem audits use only
`propext`, `Classical.choice` and `Quot.sound`.

`artifact_numerical` proves finite outputs and an absolute error at most
`2 * K * 2^-23` per cell against real matrix multiplication, for either modeled
separate or locally fused accumulation. Its `DotDomain` requires finite inputs
of magnitude at most one, a bound on every exact product, and enough remaining
range for every iteration. `standard_budget` supplies a sufficient product
budget of `1/(4K)` when `0 < K ≤ 2^20`. The proof establishes intermediate
finiteness; it does not assume it. `rectangular_exact` additionally gives bitwise
agreement with the specified separate binary32 computation under that profile.

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/leanrun --timeout 120s lake -d proofs/talos/lean build Project.WGSL.ArtifactNumerical Project.WGSL.Binary32Test
```

Native [SwiftShader CPU evidence](../../test/wgsl/evidence/macos-swiftshader/)
records successful rectangular, fusion-sensitive, signed-zero and subnormal
runs through the existing command-line harness. The rectangular shader emitted
by `tools/wgsl/Generate.lean` is byte-for-byte identical to the captured source
whose parse is proved. Runtime profile conformance remains an assumption;
the numerical theorem's input conditions remain distinct from the harness's
broader finite-input test envelope. The next integration boundary is independent
artifact-package checking, followed by the Wasm dispatch interface.

## Narrow artifact parser

`LeanExe.WGSL.Lexer` and `LeanExe.WGSL.Parse` consume the actual WGSL
text without consulting its manifest or rerendering generator output. The
restricted AST has one fixed GEMM body form. Constants, binding identities,
workgroup sizes, every body token and end-of-input are checked; the parsed
configuration must satisfy the explicit resource envelope. This accepts the
current emitted subset, not arbitrary equivalent WGSL programs.

The lexer handles all seven WGSL line terminators, all eleven blankspaces,
nested block comments and token separation. Null/BOM, malformed literals,
unknown characters, altered accesses/control flow and trailing stores fail
closed. The focused corpus includes the captured rectangular file, four
generated configurations and adversarial source mutations. It passes both
Lean evaluation and exact file-to-literal identity checks:

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/leanrun --timeout 120s lake build LeanExe.WGSL.ParseTest
tools/leanrun --timeout 60s lake env lean --run LeanExe/WGSL/ParseTest.lean
```

The corpus is regression evidence. In addition,
[RectangularArtifact.lean](../../LeanExe/WGSL/RectangularArtifact.lean)
proves that the exact captured text tokenizes and parses to the recorded AST.
Its two reductions use kernel-mode decide, not native-decide witnesses, and
compose through a reusable token-parser lemma. The file gate compares raw
bytes against the proved source's UTF-8 encoding. The source literal and
candidate token list are both explicit theorem inputs.

[Index.lean](../../LeanExe/WGSL/Index.lean) proves general row-major bounds,
unique active output addresses, coverage of each coordinate by the rounded-up
dispatch, exact u32 access arithmetic, and progress of the loop measure.
Validated dimensions imply bounded A/B/C indices and a nonwrapping loop
increment. The rectangular artifact instantiates these access bounds.
All public audits use no axioms or only standard logical axioms.

`Invocation.lean` defines entry, loop, done and error states with explicit
load/store bounds. A decreasing measure rules out every infinite transition
sequence. A preserved invariant excludes dynamic errors and relates the
accumulator and final store to `Dot`; scalar totality supplies successful
execution. `Accumulate.lean` preserves `acc + product` operand order, models
local fusion, proves profile refinement and conditional restricted exactness.

`ArtifactExecution.lean` packages the captured source's parsing theorem with
these invocation results. The source-ordered exactness theorem is conditional
on the scalar interpretation.

`Dispatch.lean`, `Launch.lean` and `Output.lean` lift the model to arbitrary
interleavings of a complete rounded-up launch. A sum of remaining work proves
termination; launch enumeration proves unique coordinates, active-cell coverage
and representable global IDs. Reachable writes are disjoint and their stores
commute. Completion reconstructs the observable buffer from those stores and
proves the dot-product relation at every active cell. The artifact package now
includes this dispatch theorem and conditional restricted bit exactness.

This is a macro-step semantics for the fixed parsed subset, with separate A/B/C
storage objects and explicit runtime progress/conformance assumptions. It does
not yet provide a concrete binary32 error bound or a Wasm/WebGPU binding theorem.
All public audits use standard logical axioms only. No new dependency is needed;
the native harness and its Linux evidence are unchanged.
