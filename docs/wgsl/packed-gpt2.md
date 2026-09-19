# GPT-2/128 with packed FP32 Wasm and WGSL

The integrated runner executes the full GPT-2 124M checkpoint. The algorithm
specification is `LeanExe.Models.Gpt2.cachedStep`. Its embedding, normalization,
attention, activations, residuals, cache construction and controller run in
Lean-generated Wasm. Four linear products per block and the two vocabulary
slices run as compiled WGSL. Tokenization and sampling run in Wasm; host C
and JavaScript provide API bindings, byte transfers and scheduling.

The restricted WGSL compiler consumes supported `Source.Kernel` definitions.
The [body compiler specification](body-compiler.md) describes those definitions.
The complete parent `ByteArray` tensor functions are not inputs to that compiler.
Checked word and byte equalities connect the compiled kernels to the parent's
actual `linearRows` and `vocabularyHead` definitions, preserving operation order
and the final bias addition.

## Run and build

From the repository root, with the local bundle and native CPU host installed:

```sh
tools/gpt2-packed --prompt 'The purpose of science is' --generate 16 --temperature 0
```

Temperature choices are `0`, `0.7`, `0.8`, and `1`; the default seed is 42 and
top-k is 40. Generation stops on token 50256 or the requested count. Requests
whose prompt and completion exceed 128 tokens are rejected before inference.

The source build entry point is:

```sh
tools/gpt2-packed build build/gpt2/packed-new
```

It requires the repository's pinned Lean/Wasm toolchain, the installed native
WebGPU/Wasmtime dependencies, and `build/gpt2/venv` with
`tools/wgsl/gpt2/requirements-build.txt` (`GPT2_BUILD_PYTHON` may override it).
The destination must be new. The gate packs the pinned checkpoint, checks the
parent proof, generates the hybrid Wasm and six shaders, checks their contracts
and controller/session proofs, and compiles the tokenizer, sampler and conversion
adapter. Wasm validation for the latter three is not a semantic proof of them.
A successful build selects its bundle for subsequent runner commands. Set
`LEANEXE_GPT2_PACKED_BUNDLE` to choose another bundle explicitly.

The browser source is available through:

```sh
tools/gpt2-packed serve 8080
```

Open `http://127.0.0.1:8080`. `tools/gpt2 serve` and `tools/gpt2-wgsl serve`
also launch this page, defaulting to port 8766.

The page offers **CPU only (Wasm, no WGSL)** and **Wasm + WGSL**, with either
an available GPU or a CPU WebGPU adapter for the latter. The CPU-only backend
loads the unchanged, checked parent `model-cpu.wasm` and requires neither
WebGPU nor shared-memory APIs. Both backends use the same checkpoint,
tokenizer, sampler, conversion adapter and generation loop.

**Compare both** runs CPU Wasm then WGSL with identical prompt/settings and
retains both completions. It checks the generated token IDs and stopping reason;
different inputs or different completions are explicitly identified. Metrics
update during each run:

- Setup, prefill, decode, first-token, sampling, text-decoding and total time.
- Prefill tokens/second and decode model steps/second. The first generated token
  uses the last prefill logits, so 16 generated tokens normally require 15
  decode steps. A one-token completion has no decode throughput measurement.
- Peak model and auxiliary Wasm linear-memory capacity, KV cache payload,
  WebGPU buffer bytes, extra host weight bytes, shared staging and dispatches.

Each run uses a fresh worker/device. Setup includes loading, compilation and
tokenization; WGSL's lazy weight uploads are part of prefill. Model-call timing
includes host transfer/wait time, but sampling/text decoding have separate
counters. Memory figures describe explicit capacities, not process RAM or
physical GPU residency; the KV cache is already included in Wasm memory.
Browser and OS caches can affect setup timing between runs.

Actual browser execution testing is pending. The desktop automation previously
reported the Mac locked; an installed headless Chromium also failed before
startup because the sandbox denied its macOS Mach-port service. The actual
host/worker CPU path has been executed under Node worker bindings and compared
exactly with the native science trace; this is not browser/WebGPU evidence.

## What the proof establishes

`Project.Gpt2Hybrid.Spec.cachedStep_exact` proves the actual hybrid controller
model computes the parent's cache and logit bytes, including rejected inputs,
ownership and cleanup. `gpt2_128_exact` and `gpt2_128_exact_for` compose reset,
weight allocation/copy, up to 128 supplied tokens, logit reads and releases.
Weights have exactly 497,759,232 bytes, token IDs are below 50,257, and the
token list has length at most 128. There is no weight-magnitude bound.

The explicit host assumption is completed execution of the certified shaders
using the declared separate FP32 operations, exact output-byte transfer, and
preservation of other Wasm store fields. Shader equality to the parent matrix
operations is proved; it is not a remaining matrix-result assumption.

The native host and browser host implementations, successful external GPU
allocation, driver conformance, tokenizer, sampler and sampling conversion
adapter are outside that theorem. WebGPU implementations may differ from the
strict arithmetic on fusion, subnormals and exceptional values. The external
Wasm parser/emitter is also a translation trust boundary. No claim is made
that the theorem proves every browser or GPU returns identical bits.

The native imports complete each dispatch before returning to Wasm. In the
browser implementation, a Wasm worker waits while the WebGPU host dispatches,
copies output to shared staging, and signals completion. The same Wasm module
and six shaders are used. GPU weight views are raw-word copies of actual Wasm
matrix offsets; the native host invalidates them on external weight writes or
reset. The model uses 50 views. Browser runs create and dispose their own host.

## Recorded execution evidence

On native CPU SwiftShader, all 6,432,896 logits across 128 contexts matched the
parent Wasm bit for bit. All 128 argmax choices agreed with PyTorch; maximum
absolute difference was 0.0015411376953125. All logits passed the test tolerance
`0.002 + 0.0001*abs(PyTorch logit)`. Complete cache arrays matched at positions
0, 1, 126 and 127. Invalid-input, cache restart and allocation/release checks
passed. The complete comparison took 113.98 seconds.

Three greedy prompt comparisons and a paired sampled completion also passed.
The sampled pair used the same Wasm tokenizer/sampler, temperature 0.8 and seed
42; both the generated text and all recorded logit bytes were identical.

The browser worker's CPU-only science run matched all 16 selected tokens and
804,112 logit words against the native trace, with WebGPU and SharedArrayBuffer
unavailable. The focused `packed-browser-test.mjs` also checks cancellation,
one-token decode counters, and cleanup after a simulated GPU setup failure.
It runs the real worker in Node; the simulated failure is not a shader test.

The [integration journal](parent-integration-journal.md) records proof attempts,
runtime measurements and remaining work. Generated models, shaders, weights,
certificates and test reports stay in `build/`, outside new source commits.
