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
  `KernelCandidate` selects the checked Lean GEMM implementation for the supported
  row-major WGSL template.
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

Both profile records select IEEE exceptional handling. The GEMM numerical
theorem proves that exceptional cases are unreachable on its advertised domain.
Runtime conformance to either profile is an explicit assumption.
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

`GptHead` selects the 1×256×4 vocabulary projection and connects independently
parsed shader dispatch to its mixed-precision specification. `HeadNumerical`
accounts for binary64-to-binary32 input conversions, separate or fused
accumulation, exact promotion, and binary64 bias addition. `GptHeadCheckpoint`
instantiates the 0.0001 head error for every four-byte input and every vocabulary
coordinate. Its reference uses the computed binary64 hidden row. `GptNumerical`
discharges the hidden-state error premise using the parent's composed theorem.
The resulting full-real-model bound is `1/10000 + 16*ErrorBudget.hidden` with
three explicit normalization denominator floors. The uniform epsilon floors
give approximately 4.85e9 per logit: this is too loose to certify precision.
Connecting all actual Wasm artifacts and executing the complete bundle remain
required.

The [native harness](../../tools/wgsl/README.md) now executes captured artifacts
and retains exact source/profile/configuration evidence. The first rectangular
kernel passed on Mesa llvmpipe; failure probes are preserved under
`test/wgsl/evidence`. These observations do not establish runtime conformance.

The [independent package gate](../../tools/wgsl/README.md) now checks the actual
shader source and all semantic manifest fields, instantiates the concrete
binary32 theorems, audits their axioms and executes the held verified input.
Its small corpus covers three matrix shapes, partial workgroups and three
rejection cases. Accepted worked packages are retained in `test/wgsl/packages`.

The Wasm dispatch boundary is now proved and runnable through the independent
bundle gate. `HostBinary` checks the exact 90-byte bridge's section encodings;
`HostMemory` proves uploads, readback and memory preservation; `HostExecution`
connects the actual small-step call to the checked shader package. Runtime
conformance remains an explicit premise. The native demonstration invokes that
Wasm function and checks the values it wrote back. Commands and worked bundles
are documented in the [native harness](../../tools/wgsl/README.md).

The parent's wider-arithmetic GPT inference and full-model error theorem are
merged. GPT artifact integration is in progress, followed by residency, tiling
and performance. The generic GEMM bundle gate still checks only the GEMM host
and shader; the complete GPT bundle gate is being implemented separately.

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
broader finite-input test envelope. Independent artifact-package checking now
passes, including the composed Wasm dispatch interface.

## Wider numerical domain and precision conversions

`WideDotDomain` replaces the small-input restriction with finite products,
an accumulator budget `C`, and a product budget `P`. With `u = 2^-24` and
`eta = 2^-150`, the per-update error is bounded by
`E = u*(C + 2*P + u*P + eta) + eta`. Its explicit premises require
`C + P + u*P + eta < 2^127` and `K*(P+E) <= C`.
`dot_error_wide` proves finite intermediates and error at most `K*E`
against real multiplication of the supplied binary32 inputs. This covers
both modeled separate and locally fused evaluation. The package and Wasm
host theorems now expose this domain alongside the original small domain;
the independent checker audits both theorem instances.

`Project.WGSL.Precision` defines pure finite-input conversion models.
Promotion preserves every finite binary32 value and its sign exactly.
Demotion uses one nearest/even rounding with gradual underflow; for finite
binary64 inputs with magnitude below `2^127`, its error is at most
`2^-24*abs(input) + 2^-150`. These are mathematical conversion models,
not a proof of native conversion externs. Fourteen promotion and twenty-one
demotion boundary vectors match both the pure model and native CPU conversion:

```sh
source tools/macos-env.sh # configured ARM Mac only
node test/wgsl/precision_test.js
```

`GptNumerical` now includes these conversion errors and the binary64 stages in
the complete real-model bound described above. The native conversion/transfer
contract remains an explicit execution assumption.

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
storage objects and explicit runtime progress/conformance assumptions. The
concrete binary32 error bound and Wasm binding theorems above compose through
this model. All public audits use standard logical axioms only.

## Complete checkpoint GPT artifact bundle

The independent GPT gate and six-case CPU corpus pass. The portable artifacts
and execution evidence are in [test/wgsl/gpt](../../test/wgsl/gpt). The selected
1×256×4 Lean GEMM definition produces the WGSL vocabulary projection. Three
exact Wasm binaries cover the hidden computation, dispatch bridge and binary64
bias addition; all have kernel-checked artifact and execution theorems.

GptBundle.artifact composes those results for every four-byte checkpoint input,
with explicit native conversion/transfer and runtime assumptions. Under the
restricted profile it gives exact mixed-precision outputs and the full real-model
bound described above. The uniform bound is approximately 4.85e9, so the theorem
is not a tight numerical accuracy certificate. The actual native corpus checks
768 output words against Lean's model and rejects altered hidden, finish and
checkpoint files. Commands are documented in [the harness guide](../../tools/wgsl/README.md).
