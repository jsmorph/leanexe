# LeanExe

LeanExe compiles a checked declaration from a restricted Lean 4 program to a standalone WebAssembly module.  The accepted language consists of monomorphic, first-order programs over supported scalar and heap representations, including bounded arrays and internal recursive data.  It supports pure computation and explicit byte I/O through `LeanExe.ByteIO`.  The [language specification](docs/spec.md) defines that language, while the [user manual](docs/manual.md) explains how to write programs within it.

LeanExe also supports direct verification of an exact WASM artifact.  Its artifact path embeds the binary bytes in Lean, decodes and validates them with checked functions, connects the decoded module to the Talos execution model, and proves a behavioral theorem about that module.  A source-agreement theorem uses Lean definitions as its specification.  The proof establishes the connection to the binary without assuming compiler correctness.

Ordinary library-mode binary serialization can also run through LeanExe's experimental [self-hosted WebAssembly emitter](docs/self-hosted-emitter.md).  The native compiler remains the production path; the LeanExe-compiled emitter is a non-blocking deterministic regression experiment.

![LeanExe architecture](docs/leanexe.png)

## Requirements

The compiler and proof workspaces pin exact Lean 4.34.0-rc2 at commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.  The proof workspace pins Talos revision `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.  The complete execution suite requires Node.js 24.13.0, Wasmtime 44.0.0, a C11 compiler, and `wasm-tools` 1.251.0.  [Developing LeanExe](DEVELOPING.md) defines the setup, process limits, version checks, and required tests.

Run every direct Lean or Lake command through `tools/leanrun`.  The runner
serializes Lean work with the neighboring VQ repository; in standard mode it
also applies the repository's CPU, memory, swap, and thread limits.  Repository
drivers that invoke Lean already use this runner for their child processes.

If a container has no systemd user scope and the user explicitly authorizes
local execution, set `LEANRUN_LOCAL=1`.  This opt-in mode still selects the
pinned toolchain, takes the shared lock, applies the command timeout,
`LEAN_NUM_THREADS=1`, `nice`, and `ionice`, and prints a warning that cgroup
CPU, memory, and swap limits are unavailable.  It never enables itself.  Put
the variable on a runner-calling repository driver instead of wrapping that
driver in `tools/leanrun`, so nested runner calls do not reacquire the lock:

```text
LEANRUN_LOCAL=1 tools/talos-artifact.js prepare <case>
```

```sh
tools/download-wasmtime.sh
tools/leanrun lake build
tools/build-wasmtime-host.sh
node test/run_all.js
```

The self-hosted-emitter experiment is not part of `run_all.js`.  Run
`node test/selfhost_emitter.js` separately only when changing its image boundary.

## Compile and run

The checked [`LeanExe.Examples.Arithmetic.choose`](LeanExe/Examples/Arithmetic.lean) declaration compiles to a scalar WASM export.  Lean remains responsible for parsing, elaboration, type checking, and declaration loading.  LeanExe accepts the declaration only when every reachable runtime term lies in the supported subset.

```lean
namespace LeanExe.Examples.Arithmetic

def choose (x y : UInt64) : UInt64 :=
  if x == 0 then y + 1 else x + y

end LeanExe.Examples.Arithmetic
```

Build the module, compile the selected declaration, and invoke the exported function with Wasmtime:

```sh
tools/leanrun lake build LeanExe.Examples.Arithmetic

tools/leanrun .lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.Arithmetic \
  --entry LeanExe.Examples.Arithmetic.choose \
  --out build/choose.wasm

build/tools/wasmtime/current/wasmtime run \
  --invoke choose build/choose.wasm 0 41
```

Scalar parameters and results use WASM `i64`.  Arrays, byte arrays, structures, and tagged values use the memory layouts and ownership rules specified in the ABI.  Pure WASI adapters provide bounded stdin, argv, stdout, stderr, and explicit error results.  `compile-wasi-io` instead runs a `LeanExe.ByteIO UInt32` entry with sequenced stdin reads and stdout writes, explicit error codes, and operation timeouts; its return value becomes the exit status.  See the [byte I/O guide](docs/manual.md#byte-input-and-output) for the required nonblocking host.

The [running-sum demo](docs/manual.md#running-sum) reads signed decimal integers
from stdin and prints the cumulative sum after each line, terminating on EOF.

The [pseudorandom generator](docs/prng.md) runs with
`tools/prng.js 42 5 100`: seed 42, five results, modulus 100.  It compiles
the Lean SplitMix64 example and prints the WASM results as decimal integers.

## Generate and verify an artifact proof

`tools/leanexegen` uses separate headless Codex tasks to generate a formal specification, a Lean program, and a proof about the compiled artifact.  Each task may iterate with Lean, while the outer tool independently checks its result.  The proof task receives the frozen specification and exact artifact model but does not receive the source program or compiler implementation.

```sh
tools/leanexegen -o myprogram.wasm myprogram.txt
tools/leanexegen --knowledge knowledge/forest.json -o myprogram.wasm myprogram.txt
tools/leanexegen verify myprogram.proof
tools/leanexegen run myprogram.wasm 10 20 30
```

The public interface for this workflow is `Array UInt64 -> Array UInt64`.  The proof package records the exact binary, decoded model, formal specification, theorem, annotations, selected knowledge packages, journal, and verification results.  The [`leanexegen` reference](docs/leanexegen.md) defines generation, verification, and the optional record, propose, and promote learning phases, while [Verifying a Program](docs/verifying.md) explains the proof boundary.

Completed proof work can produce knowledge artifacts for subsequent work.  `record` preserves a run as a worked example, while `propose` either derives one guidance or checked-support candidate or records that the run supplied no useful entry.  `promote` creates a self-contained forest snapshot after review.  A later generation or reproof selects that snapshot explicitly, and its proof package records the filtered knowledge view together with the entries the proving agent used or rejected.

## Verification boundaries

The source-driven Talos workspace contains sixty-nine registered compiler outputs, sixty-eight with completed behavioral specifications.  The complete Riemann solver proves termination, exact output, and a 512 MiB memory bound for runtime grid sizes from two to eight hundred.  Status-zero output corresponds to the specified numerical trace through time 0.8.  Thirty-eight completed registrations use raw `UInt64` binary64 interfaces and compiler-recognized floating-point intrinsics; the first five culminate in the proved guarded Euler Rusanov flux, and the sixth proves a fixed two-cell step that composes three flux calls with six conservative updates.  Its public `Project.EulerRusanovStep.Spec.sodQuarterStepCheckedBits_wat_real` theorem transfers the exact generated-WAT execution result to a decoded-real certificate: all six numeric result words are finite, both cells are Euler-admissible, and their exact values and signed rounding residuals are known.  This is a fixed-instance result, not a convergence, stability, or arbitrary-mesh theorem.  These cases do not establish support for arbitrary Lean `Float` source or agreement with Lean's native `Float` evaluator.  The separate artifact registry contains forty-three frozen WASM binaries, each with exact-byte identity, decoder and validator results, Talos translation equality, and behavioral theorems.  Euler is the first floating-point exact-byte package; the fixed two-cell step is now the second, with both execution and numerical behavior theorems.  Three additional primitive cases prove raw-word subtraction, division, and square root, including exact execution and bounded-domain numerical contracts; their frozen binary packages exercise the extended independent profile. The [verified step dataset](data/euler-rusanov-step-v1/README.md) includes raw words, exact-rational comparisons, decimal CSV, and a cell-average plot.  [Artifact Verification Format](docs/artifact-format.md) defines the binary packages and release record, [Talos Proofs](proofs/talos/README.md) owns the theorem inventory, and [Development Status](docs/status.md) records the current aggregate state and release blockers.

The knowledge forest selects versioned LTG packages containing checked lemmas, tactics, guidance, and worked examples.  Compiler annotations identify instruction regions and guide entry retrieval, while every generated theorem still checks against the decoded artifact.  [Artifact Proving](docs/artifact-proving.md), [WebAssembly Annotations](docs/annotations.md), and [Knowledge Forest and Structured LTG](docs/ltg.md) describe these components.

## Repository map

| Path | Purpose |
|------|---------|
| `LeanExe/Extract` | Checked-declaration extraction, specialization, ownership analysis, ABI lowering, and IR generation. |
| `LeanExe/IR` | First-order intermediate representation and reference evaluation. |
| `LeanExe/Wasm` | Structured WASM model, emitter, binary encoder, WAT printer, annotations, and compiler-side certificate theorems. |
| `LeanExe/Examples` | Checked source examples used by compiler and execution tests. |
| `test` | Node and Lean tests comparing source, IR, emitted WASM, and runtime behavior. |
| [Talos proofs](proofs/talos/README.md) | Source-driven behavioral proofs, exact-artifact verifier, and shared proof library. |
| [Demonstrations](demos/README.md) | End-to-end generated programs and retained artifact-proof experiments. |
| [Benchmarks](benchmarks/README.md) | Accepted, rejected, and censored proof-generation runs with journals and telemetry. |
| [Core LTG Package](ltg/README.md) | Default versioned retrieval package for proof assets and guidance. |
| [Default Knowledge Forest](knowledge/forest.json) | Default set of knowledge packages selected for proof generation. |
| [Documentation](docs/README.md) | Current user, compiler, verification, proof, and status references. |
| [Plans](plans/README.md) | Detailed plans for unfinished work governed by the root roadmap. |
| [Research papers](paper/README.md) | LaTeX sources, reviewed PDFs, bibliographies, and publication records. |

## Current work

The [GPT inference and verification guide](docs/gpt/README.md) describes the
models, goals, data flow, and source and proof directories.  The work covers
small byte-token models and pretrained GPT-2 124M.

The [four-byte model](data/tiny-gpt2-v1/README.md) returns 256 next-byte logits
from 2,488 binary64 weights.  Its checked entry validates and clips runtime
weights, with exact generated-WAT execution and numerical proofs.  Every
accepted input produces finite logits.  At weight cap ten, the universal
absolute error bound is 2,470 against real inference using the clipped weights.
The bound is too coarse to certify numerical precision.  The
[128-position tiny model](data/tiny-gpt2-128-v1/README.md)
generates byte-token text in WASM.  Its complete execution proof remains paused.

[Pretrained GPT-2 124M](data/gpt2-124m/README.md) generates text in binary32
with weights and attention caches resident in Wasmtime.  It supports up to
128 tokens.  The cached-step proof establishes exact agreement with the Lean
algorithm.  The session proof includes initialization, input encoding,
repeated calls, and buffer releases.  The binary proof connects those results
to the distributed 19,083-byte module.  Numerical error bounds remain deferred.
Retained tests compare 6,432,896 logits with CPU PyTorch over prefixes of one
to 128 tokens.

```sh
tools/tiny-gpt2.js --text 'To b'
tools/tiny-gpt2.js --context 128 --text 'ROMEO:' --generate 160
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
```

The [numerical command-line demonstrations](data/numerical/README.md) include a generated-WAT-verified exponential on [-1, 0].  Its output is finite and positive, with absolute error at most 1/4000.  The implementation accepts raw binary64 input words and executes in Wasmtime.  The extended exponential covers [-8, 0] with absolute error at most 1/300000.  The masked softmax accepts one to four scores in [-4, 4], with absolute component error at most 1/50000 and normalization error at most 32 times 2^-52.  Width-four LayerNorm accepts inputs, scales, and biases in [-4, 4], with absolute component error at most 1/1000000 and proved input and parameter perturbation bounds.  Tanh GELU accepts inputs in [-3, 3], with absolute error at most 1/80000 and input perturbation multiplier four.

The current repository has sixty-nine registered source-driven cases, sixty-eight completed specifications, sixty-nine tracked `Program.lean` caches, and forty-three exact-artifact packages, together with eleven current-interface `leanexegen` demonstrations and the original scalar demonstration.  The fifth completed floating-point case is a guarded Euler Rusanov flux with total exact generated-WAT execution, accepted-input componentwise real-error bounds, exact closure over a frozen 1,808-byte artifact, and a formally checked eight-row raw-word interface dataset.  The sixth proves total exact execution of the generated fixed two-cell step, including all three flux calls, the accepted-status gate, six exactly associated updates, seven result words, and complete store preservation.  With `ε = 2^-52`, its decoded cells are exactly left `[207/256, 9/80 - ε/20, 257/128]` and right `[81/256, 9/80 + 3ε/40, 95/128]`; both are admissible.  Their signed errors against the exact-real decoded-input quarter step are left `[0, -3ε/64, -7ε/512]` and right `[0, 5ε/64, -25ε/512]`, giving physical two-cell balance residual `[0, ε/32, -ε/16]`.  Its exact 2,551-byte package and verified raw step dataset are complete; Wasmtime host generation and C comparisons are regression evidence, not part of the formal theorem.  Demo 12 adds a bounded first-zero search and a variable-length copy-and-shift result over artifact digest `7cdd8adba75d4f076d0a142f824a19a0d34d6a5cedd1a810a417a7fc5789f7b6`.  Its independently verified clean reproof used seven LTG entries without rejection and replaced all local search and copy-loop invariants with `FixedArrayFindIdxEq.program_spec` and `FixedArrayCopy.eraseIdxProgram_spec`.

The reproof took 3,987.145392 seconds in Stage 5 against the 3,907.231311-second baseline, an increase of 2.045 percent, while reducing the proof from 860 to 607 lines, 3,516 to 2,587 words, 39,249 to 28,874 bytes, and 47 to 38 journaled checks.  The journal then produced shared theorems for a dynamic array-header length store and the encoded-index comparison with one.  The retained measurement package keeps the tool pins from that run, while a current-ProofKit re-freeze preserved the artifact digest and passed independent verification after the helper additions.  Erase setup and branch-aware result transfer remain the general proof boundaries, while the [Demo 12 record](demos/demo-12/README.md) preserves the package and detailed comparison.

The 2026-09-19 aggregate artifact check passed all forty-three frozen packages, their behavioral specifications, and registered declaration audits.  The checked-in twenty-one-package release draft remains historical and does not record that run.  Semantic conformance, an immutable source revision, and cold-checkout evidence remain separate release work.  [Development Plan](plan.md) is the work queue, and `devnotes.md` records decisions and test evidence.

The Euler agenda now includes [two-dimensional flow visualizations](data/euler-2d-v1/README.md):
192 × 192 circular-pulse and quadrant problems with density, pressure and
schlieren views, 21-frame standalone animations, SVG/PNG posters and
reproducible raw data. Every numerical WASM module has exact-byte proofs;
native orchestration is independently checked against all saved raw values.

The [four-state Riemann experiment](data/euler-riemann-v1/README.md) uses the
Lanyon article's initial states and interface positions on a 192 × 192 grid
through time 0.8.  Its short article includes final density and pressure
figures, the extended admissibility check, numerical diagnostics, and
reproducible data.

The [complete WASM Riemann calculation](data/euler-riemann-complete-v1/README.md)
has kernel-checked proofs covering the frozen binary from initialization
through final output, including termination and the 512 MiB memory bound.
Both the 192 × 192 and 800 × 800 runs returned status zero at time 0.8
using that binary.  Their density and pressure figures and raw data are complete.

The [2D hyperbolicity proof](proofs/talos/README.md#two-dimensional-euler-hyperbolicity)
establishes the physical flux derivative and a complete real eigenbasis in
every spatial direction at positive-density, positive-pressure states for
gamma 7/5.  The exact-binary solver theorem applies it to accepted states,
intermediate sweep grids, and terminal cells.

The [reconstructed solver](plans/euler-mathematical-parity.md#6-complete-revised-solver-and-data)
now has complete exact-byte proofs and an accepted independent package
check.  Its 30,726-byte module adds positivity-limited minmod reconstruction,
outward characteristic-speed bounds, and checked CFL conditions.  Its
accepted trace has state and face safety, hyperbolicity, and conservation
with bounded rounding residuals.  Both revised production grids use eight
reconstruction attempts.  The [192-grid and 800-grid data and figures](data/euler-reconstructed-v1/README.md)
are complete.  Both runs returned status zero at time 0.8, in 176.7 seconds
and 3 hours 58 minutes respectively.  The short article includes their
comparison and the claim-to-theorem table.

The [net conservation-error observer](plans/euler-certificates-and-convergence.md)
adds interval bounds for mass, both momenta, and energy.  Its source proofs
connect the computed bounds to the existing conservation residual and
prove that it preserves the solver's numerical output.  Complete observer
WASM execution, allocation, exact output, and the 512 MiB memory bound now
have checked proofs.  Exact-byte proofs remain in progress.
The generated totals and boundary-contribution functions have exact execution
and store-preservation proofs.  Checked function-region equality reuses the
previous sweep, initialization, output, and release proofs.
The trial and retry functions now have complete execution proofs, including
all failure paths, exact interval results, and heap reservations.  The complete
time-step loop and enclosing run now prove exact generated execution through
initialization, final totals, and the four residual intervals.  Final packing
and the exported entry also pass.  The focused source-artifact gate passes
for the unchanged 45,644-byte module.  The exact-byte package remains open.
