# Gpt32: GPT-2 in binary32 on WGSL and PTX

## One GPT-2 step as WGSL kernels

[The program](Program.lean) is one generation step of GPT-2 124M in Lean `Float32`, binary32,
written for GPU kernels: it builds every array element by element and marks the helpers that kernels
share `@[inline]`, so that `verified_compile` unfolds them into each kernel.  Its kernel functions
are `expArray32` through `logits32`, and `step32` composes all of them but `expArray32` into the
embedding, the layers of attention and MLP, the final layer norm, and the token scores.  Vector
addition and the biased linear transform come from [the binary32 linear-algebra
library](../../Library/Numerics/LinearAlgebra/README.md), and the model-specific kernels and the
host program remain in the demo.  [The host program](HostProgram.lean) is the list of commands that
runs a step in the sessions of `leanexe-webgpu-host` and `leanexe-cuda-host`: buffer loads, word and
float constants, and kernel runs.

## Verified compiler

[The verified compilation](Verified.lean) compiles the kernel functions with `verified_compile`,
and `tests/verified/run.sh` writes the module to `build/verified/gpt32.wasm`.  For each function
`f`, the generated theorems `compiled.f.implements`, `compiled.f.trapFree`, and
`compiled.f.bound_eq` state execution, trap-free execution under the allocation bound, and that
bound, and `compiled.bytes` states that the module's bytes decode to the module.  The compilation
also passes each function's typed body to `Verified.WGSL.compile`, which returns a WGSL compute
kernel with proofs of its translation and uses the shared WGSL translation, which normalizes
arithmetic NaNs to `0x7fc00000`.  [The dispatch theorems](VerifiedDispatch.lean)
combine `Compiled.dispatch_value` with each generated denotation equation `compiled.f.denote_eq`,
so that a dispatch of each kernel computes its Lean function.  [The kernel
map](VerifiedKernels.lean) names the kernel of each host call, and [the WGSL
host](VerifiedHost.lean) defines `device`, the device of `leanexe-webgpu-host`, and `backend`, its
`Backend`, from their dispatch theorems.
[The verified compiler manual](../../docs/verified-manual.md#wgsl-kernels) gives the subset that
the translation accepts and the conditions of its dispatch theorem.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, `compiled.f.trapFree` | For each compiled function `f`, `gpt32.wasm` computes `f` bit for bit, unless the call stops at `unreachable`, and without that stop when `top` is at least `compiled.f.bound` bytes below the memory cap. |
| `compiled.bytes` | `encode` succeeds on `compiled.module`, `decode` reads the bytes back as the module, and the module implements every compiled function. |
| `gpt32_file`, `gpt32_file_decode` | `build/verified/gpt32.wasm` holds `encode compiled.module` and decodes to `compiled.module`.  [`File.lean`](File.lean) checks both after the file is written. |
| `embedKernel_dispatch` and the other dispatch theorems | Under bounds below `2^29` on the input sizes and the output count, with an output buffer that has the length header and a slot for every element, and with enough invocations to cover the output, a dispatch of each kernel leaves its Lean function of the inputs in the output buffer and is race-free. |
| `Demos.Gpt32.generate_host` | For a device with a backend, under bounds on the shape and the tokens, for weights loaded from the files and a prompt of fewer than 1,024 tokens, the commands of `setupItems`, the steps of the prompt, and one more step run without error, every run meets the device's memory model, and the commands leave the scores of `step32` for the last token in the output buffers. |
| `Demos.Gpt32.Verified.generate_host` | `Demos.Gpt32.generate_host` for the WGSL kernels of the verified compilation: every dispatch is race-free, a consistent execution of it under the statement of the Vulkan memory model exists, and in every one no access is in a data race, every invocation ends, and the reads after the dispatch read its output. |
| `embedKernel_launch` and the other launch theorems of `Demos.Gpt32.VerifiedPtx` | Under the bounds of the matching dispatch theorem, the sequential run of a launch of the PTX kernel with at least as many threads as output elements leaves the Lean function's result after the count and is race-free, and in every consistent execution under the PTX memory model no access of a thread is in a data race, every thread ends, and the copy back reads that result. |
| `Demos.Gpt32.VerifiedPtx.generate_host` | `Demos.Gpt32.generate_host` for the PTX kernels: every launch is race-free, a consistent execution of it under the PTX memory model exists, and in every one no access of a thread is in a data race, every thread ends, and the copy back reads the launch's output. |

[The PTX compilation](VerifiedPtx.lean) translates the same bodies with `Verified.PTX.compile`.
Each launch theorem takes the bounds of the WGSL dispatch theorem of its kernel, whose `Spec.Fits`
proof, such as `embedGpu_fits`, it shares through `Verified.PTX.Compiled.of_wgsl`: a build that both
compilers translate has one kernel plan.  [The PTX kernel map](VerifiedPtxKernels.lean) names the
PTX kernel of each host call, and [the PTX host](VerifiedPtxHost.lean) defines the device of
`leanexe-cuda-host` and its backend from the launch theorems.

## The host theorem and the device model

`Demos.Gpt32.generate_host` holds for any `Device` with a `Backend`.  A device gives the buffers
of the host commands, the run of a kernel, and `Meets`, the statement of the device's memory model
about one run, and a backend gives the run of each host call from its kernel's theorem.  The host
theorem composes these with [`Exec.lean`](Exec.lean), which gives meaning to the typed items of the
host program and to their host commands and shows that a run of the items is a run of their
commands, and with [`Compose.lean`](Compose.lean), which proves what the eighteen kernel calls of a
layer compute.  `Demos.Gpt32.Verified.generate_host` instantiates it with the WGSL device and
`Demos.Gpt32.VerifiedPtx.generate_host` with the PTX device, so the commands, run with the verified
kernels, leave the bits of `step32`, the Lean step, in the score buffers.

The theorems prove successful execution in device models with strict binary32 arithmetic, under
their shape, buffer, and token bounds.  `Meets` states the memory model for each run separately,
from the buffers that the commands before it leave, and `generate_host` composes the runs in the
sequential model.  The order of WebGPU's queue and of a CUDA stream joins the runs, as [the trust
document](../../docs/trusted-base.md) states.  A GPU may flush subnormal values and fuse
multiply-adds, as the WGSL specification permits, while the PTX kernels round each operation as the
ISA's `.rn` instructions do.  Under SwiftShader in headless Chromium 145, the verified kernels and
`gpt32.wasm` gave equal scores at every step of 16 greedy tokens, as [the description of the
pages](../../tests/web/README.md) records.  On an NVIDIA GB10 with CUDA 13.0, the PTX kernels gave
the scores of native `step32` bit for bit on the models of `tests/gpt32/native.sh`, and with the
weights of GPT-2 124M, 16 greedy tokens after "The meaning of life is" chose the tokens of Hugging
Face's float32 model, with a largest score difference of 8.76e-6 relative to the largest score.
All scores of those steps equaled the scores of `gpt32.wasm` bit for bit.  [The design document](../../docs/design.md#gpu) states what the device model adds to
the trusted base, and [the description of the pages](../../tests/web/README.md) states what is
proved about the browser page.  The proofs do not cover the host processes, file I/O, and browser.

## Building, running, and testing

```sh
tools/leanrun --timeout 20m lake build Demos.Gpt32.VerifiedHost Demos.Gpt32.VerifiedPtxHost
tools/build-webgpu-host.sh
tests/verified/run.sh --cases gpt32
tests/wgsl/run.sh
tests/gpt32/native.sh
uv run tests/gpt32/generate.py --tokens 8 "The meaning of life is"
uv run tests/web/serve.py
```

The commands build the proofs and the WebGPU host, test the module and the kernels, generate text,
and serve the browser pages, with the setup of [the repository README](../../README.md#commands).
On a machine with an NVIDIA GPU and the CUDA toolkit, these commands build the CUDA host, test the
PTX kernels, and generate text with them:

```sh
tools/build-cuda-host.sh
tests/ptx/run.sh
tests/gpt32/native.sh --devices cuda
uv run tests/gpt32/generate.py --driver cuda --tokens 16
```

`tests/verified/run.sh --cases gpt32` writes the module and compares it with native Lean on the Wasm
cases of [the checked kernel corpus](VerifiedCases.lean).  The corpus covers empty and short arrays,
signed zeros, subnormals, infinities, and NaNs, and its Wasm cases also check allocations and
retained blocks.  Without `--cases`, the verified driver also checks `File.lean` against the file
it wrote and requires the axiom reports of both file theorems to name only `propext`,
`Classical.choice`, and `Quot.sound`.  `tests/wgsl/run.sh` runs the kernels, with the binary32
example's verified kernels, on the cases of [`tests/wgsl/Cases.lean`](../../tests/wgsl/Cases.lean)
and of the corpus on the SwiftShader and llvmpipe Vulkan drivers, and compares each output word
with native Lean's.

[`tests/gpt32/native.sh`](../../tests/gpt32/native.sh) runs small random models through `generate`
of [`Driver.lean`](Driver.lean), the driver that [`Generate.lean`](Generate.lean) runs, on the
devices that `--devices` names: the verified `gpt32.wasm`, both Vulkan drivers, and the CUDA host,
by default all but CUDA.  It compares every score bit and each greedy token with native `step32`.
For CUDA, the driver writes the PTX text of each kernel and compiles it with `ptxas -O3
--fmad=false`, and the script records the SHA-256 of each cubin.  Its Wasm session adapter,
[`tools/gpt32-wasm-host.mjs`](../../tools/gpt32-wasm-host.mjs), uses the Wasm host of the browser
page, [`hosts.js`](../../tests/gpt32/browser/hosts.js).
[`tests/gpt32/generate.py`](../../tests/gpt32/generate.py) writes the pinned checkpoint's weights
to `build/gpt2-32/`, 949 MiB, and generates text greedily on the device that `--driver` names: a
Vulkan driver with the WGSL kernels, which `Generate.lean` writes to `build/wgsl`, the CUDA host
with the PTX kernels, which it writes to `build/gpt32-ptx`, or `gpt32.wasm`.  For each step it
reports the largest score difference from Hugging Face's float32 model, relative to the largest
score, and whether the two models choose the same token, and `--compare` compares the scores bit for
bit with those of an earlier run on another device.  The script has run with the PTX kernels and
`gpt32.wasm` and not with the WGSL kernels.  `tests/web/serve.py` serves the kernels,
`build/verified/gpt32.wasm`, and the verified sampler module `build/verified/gpt.wasm` to the
browser pages.

## Related examples

[`Gpt`](../Gpt/README.md) is the same model in binary64 on WebAssembly, with theorems about the
bytes, and the GPT-2 browser page samples tokens with its `sampleTopK`.
[`Binary32`](../../Examples/Binary32/README.md) has the verified WGSL kernels of `scale32`,
`axpyArray32`, `matVec32`, and `condMix32`, which `tests/wgsl/run.sh` runs with this demo's kernels.
The VKB entry [`verified-wgsl-kernel`](../../VKB/entries/verified-wgsl-kernel/README.md) describes
how a build compiles to a WGSL kernel and how its dispatch theorem is proved.

## References

- A. Radford, J. Wu, R. Child, D. Luan, D. Amodei, and I. Sutskever, "Language Models are
  Unsupervised Multitask Learners," OpenAI, 2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/),
  [§15.7.2](https://www.w3.org/TR/WGSL/#differences-from-ieee754) and
  [§15.7.5](https://www.w3.org/TR/WGSL/#reassociation-and-fusion).
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/).
- gfx-rs, [wgpu-native](https://github.com/gfx-rs/wgpu-native).
