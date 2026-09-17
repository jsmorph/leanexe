# Native WGSL test harness

`run.py` executes the exact UTF-8 WGSL file with wgpu-native through pinned
wgpu-py. It needs no browser and prefers a CPU adapter when one is available.
The initial ABI is row-major binary32 A/B/C storage buffers and the `gemm_f32`
entry point described by the generated JSON manifest. The harness accepts
arbitrary supported binding indices/groups and two-dimensional workgroups.

## Generate, independently verify, and run

From the configured repository root, this single command generates the supported
Lean GEMM candidate, checks its exact artifact package, and executes the checked
input snapshot on the CPU:

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/artifact-proof.js wgsl-build build/wgsl/my-verified-gemm 3 5 2 separate
```

The output directory must be fresh. Each verification attempt under
`build/wgsl/package-checks` retains its exact
shader/manifest snapshots, generated proof, diagnostics, axiom audit and receipt.
The native report records all input/output words and runtime configuration.

Existing packages can be checked without the generator or runtime, or checked
again and executed:

```sh
tools/artifact-proof.js wgsl-check test/wgsl/packages/rectangular
tools/artifact-proof.js wgsl-run build/wgsl/my-verified-gemm
tools/artifact-proof.js wgsl-corpus build/wgsl/my-verified-corpus
```

The six-case corpus is fixed in `tools/wgsl/corpus.json`: scalar, rectangular and
partial-workgroup kernels, followed by rejection of a changed store, mismatched
dimensions and extra metadata. It runs Lean checks sequentially through
`tools/leanrun`; it does not run the unrelated project regression suite.

The generator's output is not trusted. `Prepare.lean` reads the actual files and
produces an untrusted proof draft. A separate Lean invocation kernel-checks the
lexer result, parser result, resource bounds and every semantic manifest field.
The reusable `Project.WGSL.Binary32.Package` then supplies dispatch termination,
memory safety, GEMM correspondence, conditional numerical bounds and restricted
exactness. Only the three standard logical axioms are accepted; native decision
axioms and `sorryAx` are rejected.

The file checker compares the embedded shader bytes and manifest bytes against
the snapshots. JSON decoding and that filesystem comparison are checker
operations, outside the kernel theorem; typed metadata agreement is proved.
The runner's JSON interpretation must equal the checked metadata, including the
complete field set. For execution, the gate passes its held shader/manifest text
directly to `run.py --snapshot-stdin`, avoiding another filesystem read between
verification and dispatch. The native report must identify that same input.
Runtime conformance to the selected profile remains an explicit assumption.

## Checkpoint GPT bundle

The selected Lean vocabulary projection is a 1×256×4 binary32 GEMM. The
checkpoint GPT path executes the hidden computation in Wasm, explicitly converts
its four binary64 results and the head weights to binary32, dispatches that WGSL
kernel, then executes the binary64 bias addition in a separate Wasm artifact.
Only this supported projection is selected for WGSL generation.

From a configured proof workspace:

```sh
tools/artifact-proof.js wgsl-gpt-build build/wgsl/my-gpt-bundle
tools/artifact-proof.js wgsl-gpt-run build/wgsl/my-gpt-bundle 76 101 97 110
tools/artifact-proof.js wgsl-gpt-check build/wgsl/my-gpt-bundle
tools/artifact-proof.js wgsl-gpt-corpus build/wgsl/my-gpt-corpus
```

Build and corpus destinations must be fresh. The gate independently checks the
actual shader and manifest, all three exact Wasm artifacts, and all 2,488
checkpoint words. It binds that shader package to GptBundle.artifact and audits
the proof dependencies against the three standard logical axioms. Existing
receipts and supplied proof files cannot authorize execution. First-time proof
builds can require staged dependency preparation; a build timeout is a failure,
never permission to skip verification.

The six-case GPT corpus checks all 256 logits for three byte-token inputs against
Lean's integer floating-point model, then checks rejection of changed hidden
Wasm, bias-addition Wasm, and checkpoint bytes. One verified input snapshot is
shared by the three executions. Exact output comparison uses the separate
binary32 profile; a driver that contracts multiply/add is not silently accepted.

The theorem covers every four-byte input for this checkpoint. Its head-only
error bound is 0.0001 against the real head applied to the computed binary64
hidden row. The composed bound against the full real GPT model is approximately
4.85e9 per logit: mathematically proved but too loose to certify useful precision.
Native conversions and orchestration, Node's Wasm engine, and the native WebGPU
implementation remain explicit conformance assumptions. The runtime tests do
not establish those assumptions universally.

## Resident GPT session and head measurements

Repeated contexts can share one native process, immutable head weights and one
pipeline while retaining the same verified Wasm imports and output contract:

```sh
tools/artifact-proof.js wgsl-gpt-session test/wgsl/gpt 76 101 97 110 0 0 0 0 255 128 1 0
tools/artifact-proof.js wgsl-gpt-benchmark test/wgsl/gpt build/wgsl/my-head-benchmark
```

The session accepts one to sixteen groups of four byte tokens. The bundle is
independently verified once, every output is compared with Lean's model, and
native shutdown completes before success. A changed Wasm weight snapshot is
rejected before resident dispatch. Native startup time is recorded separately
from warm context timings; verification and reference generation are excluded
from those timings.

The benchmark checks five generated GEMM candidates, comparing pipeline/weight
recreation with residency and three one-row dispatches with one three-row
kernel. Every candidate has its own independent artifact check. The fixed
configuration has two warmup rounds and nine measured rounds, with all outputs
checked. See [measurements and decisions](../../docs/wgsl/performance.md) for the
CPU-only scope, exact timing boundaries and retained artifacts.

## Verified Wasm + WGSL bundle

The complete GEMM path starts in a real Wasm function, dispatches the checked
WGSL through native WebGPU, and copies the result back into Wasm memory:

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/artifact-proof.js wgsl-bundle-build build/wgsl/my-gemm-bundle 3 5 2 separate
tools/artifact-proof.js wgsl-bundle-check build/wgsl/my-gemm-bundle
tools/artifact-proof.js wgsl-bundle-run build/wgsl/my-gemm-bundle
tools/artifact-proof.js wgsl-bundle-corpus build/wgsl/my-bundle-corpus
```

`wgsl-bundle-build` requires a fresh directory. `wgsl-bundle-check` independently
checks an existing package without executing it; `wgsl-bundle-run` checks it
again before execution. Each attempt retains the exact `host.wasm`, shader and
manifest, `BundleProof.lean`, axiom reports, verification receipt and execution
report. Existing receipts and supplied proof files are never used as authority.

The 90-byte host exports `memory` and `run(aOffset, bOffset, cOffset)`. Its import
is `leanexe.webgpu.gemm_f32(i32, i32, i32) -> i32`; zero means completed success.
Offsets are unsigned byte addresses, aligned to four bytes. All three regions
must fit in Wasm memory. Each buffer is capped at 16,384 words and each dispatch
at 262,144 multiply/add iterations. Both inputs are copied before the result is
written, so input/output regions may overlap. The default demonstration uses
small dyadic inputs, compares every output, and checks all bytes outside C.

The Lean checker proves the exact Wasm section encodings, including its function
import; the standard Wasm engine also validates the module before instantiation.
`HostExecution` composes the authoritative Wasm small-step rules with the
independently checked WGSL package. The resulting theorems establish termination,
final Wasm `read32` results, and the same conditional numerical bound as GEMM.
The file-identity checks compare actual bytes with the checked constants. The
runner instantiates those held bytes and passes the held shader text to the
native worker over stdin.

The theorem assumes `HostExecution.contract`: correct input snapshots, native
dispatch conforming to the selected profile, completed readback, and the stated
memory update. The JavaScript/Python adapter, Node's Wasm engine, shader compiler
and native driver are outside the formal proof. Runtime tests exercise that
boundary; they do not prove universal conformance. No additional dependency was
introduced for the Wasm bridge.

The bundle corpus uses the same three positive matrix shapes and rejects altered
Wasm bytes before instantiation. Four small JavaScript tests exercise argument
order, byte order, aliasing, invalid addresses and rejection before output writes:

```sh
node --test test/wgsl/host_test.js
```

Worked bundles and their retained reports live in `test/wgsl/bundles`.

## Direct generation and execution on this ARM Mac

The checked local CPU route is `run.py → wgpu-native → Vulkan → SwiftShader`.
It runs as a command-line process, without a browser, Metal or virtual machine.
Generate the supported Lean GEMM candidate and run its exact emitted shader:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 60s lake env lean --run tools/wgsl/Generate.lean build/wgsl/my-gemm 3 5 2 separate
tools/wgsl/run-macos-cpu.sh build/wgsl/my-gemm/kernel.wgsl build/wgsl/my-gemm/manifest.json \
  --report build/wgsl/my-gemm/execution.json
```

Choose fresh artifact/report paths; previous results are retained. The generator
uses the existing checked `gemmCandidate` interface and fixed GEMM template.
The `3 5 2` arguments mean a 3×2 matrix times a 2×5 matrix.

The installed defaults use the isolated environment
`build/wgsl/macos-venv-20260916` and SwiftShader's libraries from the existing
Chrome 152.0.7977.84 installation. Chrome itself is never launched. Override
`LEANEXE_WGPU_PYTHON`, `LEANEXE_WGPU_NATIVE_LIB` or `LEANEXE_SWIFTSHADER_DIR`
to select another installation explicitly. There is no automatic backend fallback.

The standard wgpu-native macOS binary does not enable Vulkan. The optional
`tools/wgsl/build-macos-cpu.sh` setup command installs checksum-pinned Rust 1.90.0
inside `build/tools`, then builds wgpu-native commit
`768f15f6ace8e4ec8e8720d5732b29e0b34250a8` with its locked dependencies and one
build job. The pinned release needs **both** `vulkan-portability` and
`wgc/vulkan-portability`; the outer feature alone fails to enable Vulkan in its
core library. No upstream source modification is needed. This setup requires
Apple command-line build tools already installed on the host.

The approved Python environment uses the five versions in `requirements.txt`
and macOS transitive dependency `rubicon-objc==0.5.6`. To prepare another isolated
Python 3.14 environment, install that set there and select it with
`LEANEXE_WGPU_PYTHON`. The setup script does not install Python or SwiftShader.

Recorded [CPU execution evidence](../../test/wgsl/evidence/macos-swiftshader/)
includes all 15 rectangular GEMM outputs plus fusion-sensitive, signed-zero and
subnormal cases. Every checked word belongs to its manifest's reference relation.
`runtime.json` identifies the source revision, build features, toolchain archives
and actual native/driver library hashes. These runs do not prove universal
runtime conformance to either restricted profile.

## Other native environments

Create an isolated environment, then install the pinned dependency set:

```sh
python3 -m venv /tmp/leanexe-wgsl-venv
/tmp/leanexe-wgsl-venv/bin/python -m pip install -r tools/wgsl/requirements.txt
```

For the checked Linux x86_64 / CPython 3.14 environment, use
`tools/wgsl/requirements-linux-cp314.lock` instead; it additionally requires the
recorded SHA-256 hashes of all five dependency wheels.

Given an emitted artifact and manifest, run:

```sh
tools/wgsl/run.py build/wgsl/gemm.wgsl build/wgsl/gemm.json \
  --python /tmp/leanexe-wgsl-venv/bin/python \
  --report build/wgsl/execution.json
```

Use `--backend Vulkan --adapter llvmpipe` to require Mesa Lavapipe, or
`--backend OpenGL --adapter llvmpipe` for Mesa's native software OpenGL adapter.
No matching adapter, missing dependencies, invalid shader, timeout, and numerical
mismatch all produce a nonzero exit code and an evidence report. Driver
diagnostics are preserved. Adapter discovery/compilation/dispatch/readback run in
a child process with a default 30-second timeout (`--timeout`, maximum 300).
The parent imposes bounded buffer sizes, GEMM work, and exhaustive reference
enumeration. These engineering limits are narrower than generation limits.

The default input generator is a specified 32-bit LCG with finite normal values
and signed zeros. `--seed` reproduces it. `--vectors path.json` instead loads exact
eight-digit hexadecimal binary32 words in `{ "a": [...], "b": [...] }`; values
must be finite with magnitude at most 16. Example 1x1x2 inputs are checked in at
`test/wgsl/vectors/` for fusion, signed-zero accumulation, and subnormals.

The two supported profile ids, both at revision 1, are:

* `leanexe-f32-rne-separate-v1`: source-ordered separate multiplication/addition,
  round-to-nearest ties-to-even, preserved subnormals, IEEE signed zero.
* `leanexe-f32-rne-fusion-v1`: each source-ordered accumulation step may use either
  a separate multiply/add or one fused multiply-add, with the same scalar rules.

The Python reference uses exact rational arithmetic and integer nearest-even
rounding. The fusion profile exhaustively propagates the permitted accumulator
set; exceeding its state/work cap is an error, never an approximate acceptance.
The checker compares bit patterns, including signed zero. It supports neither
general reassociation nor flushing subnormals. Native implementations may fail
these deliberately restricted profiles even when conforming to WGSL.

Reports capture shader text and SHA-256, manifest and hash, exact input/output
words, permitted output sets, profile/WGSL revisions, dispatch/bindings, timeout,
native library hash/version, Python packages, adapter/device information,
selected driver environment variables, and diagnostics. Successful membership
is evidence only for the tested execution. Neither a successful test nor these
identifiers prove universal runtime conformance or a Lean artifact theorem.
The formal scalar model must be connected independently to these numerical
policies. There is currently no proved real-valued error bound in this harness.

The dependency-free regression suite covers IEEE rounding boundaries, signed
zero, subnormals, fusion-sensitive results, rectangular indexing, deterministic
buffers, manifest rejection, and preservation of error evidence:

```sh
python3 test/wgsl/reference_test.py
```

The native API follows the upstream
[wgpu-py 0.31.1 compute example](https://github.com/pygfx/wgpu-py/blob/v0.31.1/examples/compute_noop.py).
The numerical-policy source is the pinned
[17 August 2026 WGSL floating-point evaluation draft](https://www.w3.org/TR/2026/CRD-WGSL-20260817/#floating-point-evaluation).
