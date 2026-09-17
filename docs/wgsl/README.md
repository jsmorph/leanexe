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
these parametric lemmas. The new index theorems establish bounds and unique
addresses, but their connection to concurrent execution, termination and
numerical behavior remains an explicit next obligation.

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
2. Instantiate operational semantics for the parsed body and connect the
   checked indexing/dispatch lemmas to loads, stores, unique writes and termination.
3. Instantiate binary32 arithmetic and prove execution correspondence under
   the selected numerical profile.
4. Prove GEMM numerical bounds and restricted exactness, then independently check
   the exact artifact package.
5. Add the Wasm dispatch boundary, bundle composition, and mixed-precision GPT-2
   integration before doing residency, tiling, and performance work.

The existing pinned Talos dependency has pure binary32 operations and numerical
lemmas. Reuse belongs in the existing proof workspace, preserving its dependency
and license boundary rather than copying third-party source into the compiler.

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

These results do not yet constitute a complete WGSL execution, concurrent
race-freedom, termination or numerical theorem. No new dependency is needed;
the native Python harness and its Linux evidence are unchanged.
