# Verified head performance experiments

These measurements use the configured ARM Mac's SwiftShader CPU device through
native WebGPU. They do not predict physical-GPU throughput. Every shader is a
generated instance of the supported Lean GEMM definition and passes the
independent artifact gate before measurement. No new WGSL operations or Wasm
binaries are introduced by the benchmark.

## Fixed experiment

The three inputs are the same four-byte contexts used by the GPT corpus. Their
hidden rows are checked against Lean's integer floating-point model before use.
All candidates compute three vocabulary projections, either as three one-row
dispatches or one three-row dispatch. Each native output word is compared with
the exact separate binary32 reference. C is reset to a NaN sentinel before every
dispatch so a missing write cannot reuse an earlier correct result.

The benchmark alternates the order of the recreate and resident paths, with two
warmup rounds and nine measured rounds. It checks 84,480 output words across the
five candidates. Timers include input upload, submission and synchronous
readback; the recreate path also includes buffer/pipeline creation and disposal.
They exclude process/device startup, artifact verification and reference
arithmetic. Resident setup is recorded separately.

| Kernel / workgroup | Recreate, ms per 3 inputs | Resident, ms per 3 inputs |
| --- | ---: | ---: |
| One row, 8×8 | 17.926 | 0.300 |
| One row, 32×1 | 17.854 | 0.276 |
| One row, 64×1 | 18.374 | 0.281 |
| Three rows, 32×1 | 6.151 | 0.121 |
| Three rows, 64×1 | 6.082 | 0.120 |

These are medians from one run, not confidence intervals. The 32- versus 64-wide
differences are too small to justify choosing between them from this run. The
original 8×8 GPT artifact remains supported. The stronger findings are the cost
of recreating the pipeline and the benefit of batching these small projections.

The portable shaders, manifests and recorded reports are in
[test/wgsl/head-performance](../../test/wgsl/head-performance). Historical reports
include the original local proof-attempt paths. They are evidence, not authority
to skip a fresh artifact check.

## Resident complete-GPT execution

The resident command verifies the full GPT bundle, then processes a bounded
sequence of one to sixteen four-byte contexts using one native process, one
immutable weight buffer and one pipeline. Every context still invokes the exact
hidden Wasm, exact dispatch-bridge Wasm and exact bias-addition Wasm. Each Wasm
import passes its actual A snapshot to the resident kernel and checks that its B
snapshot equals the resident weights before dispatch. Readback completes before
the bridge writes C. Native process shutdown completes before success is reported.

A Node worker owns the native process because the proved Wasm import is
synchronous. Its bounded shared response carries the completed result to that
import. The Wasm ABI and formal execution contract are unchanged. The adapter,
conversions and native engines remain explicit conformance assumptions.

Stage timings in GPT execution reports exclude Lean reference generation and
artifact verification. Native process/device/pipeline startup is recorded
separately as `nativeStartupMs`; it can overlap reference preparation. Warm
per-context timings must not be presented as cold end-to-end latency.

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/artifact-proof.js wgsl-gpt-session test/wgsl/gpt 76 101 97 110 0 0 0 0 255 128 1 0
tools/artifact-proof.js wgsl-gpt-benchmark test/wgsl/gpt build/wgsl/my-head-benchmark
```

The benchmark destination must be fresh. Both commands perform their own
independent artifact checks and retain new evidence.

## Decisions within the CPU execution scope

Keep weights and the pipeline resident for repeated inference. The session
implements that decision in the complete GPT path. Batched 3×256×4 GEMM kernels
are additional checked artifacts and demonstrate batching's benefit in the head
benchmark. Their generic GEMM theorems are distinct from the complete one-row
GPT bundle theorem; the benchmark does not claim a new full-GPT batch theorem.

Retain the separate binary64 bias-addition Wasm. Its arithmetic is part of the
proved mixed-precision contract, and measured work is dominated by native setup
and dispatch rather than that small Wasm call. Additional nonlinear WGSL
operations or shared-memory tiling would require new semantics and proofs; this
measurement supplies no reason to expand the supported subset for this head.

Physical-GPU conformance testing is outside this run's explicit CPU-only scope.
The full-model error bound remains approximately 4.85e9 per logit, despite the
head-only bound of 0.0001. These performance changes do not improve that bound.
