# Gpt32: GPT-2 in binary32 on WGSL

## One GPT-2 step as WGSL kernels

[The program](Program.lean) is one generation step of GPT-2 124M in Lean `Float32`, binary32,
written for GPU kernels: every array is built element by element, and the helpers that kernels
share are marked `@[inline]`, so that `verified_compile` unfolds them into each kernel.  Its kernel
functions run from `expArray32` to `logits32`, and `step32` composes all of them but `expArray32`
into the embedding, the layers of attention and MLP, the final layer norm, and the token scores.
Vector addition and the biased linear transform come from [the binary32 linear-algebra
library](../../Library/Numerics/LinearAlgebra/README.md), and the model-specific kernels and the
host program remain in the demo.  [The host program](HostProgram.lean) is the list of commands that
runs a step on `leanexe-webgpu-host`: buffer loads, word and float constants, and kernel
dispatches.

## Verified compiler

[The verified compilation](Verified.lean) compiles the kernel functions with `verified_compile`,
and `tests/verified/run.sh` writes the module to `build/verified/gpt32.wasm`.  For each function
`f`, the generated theorems `compiled.f.implements`, `compiled.f.trapFree`, and
`compiled.f.bound_eq` state execution, trap-free execution under the allocation bound, and that
bound, and `compiled.bytes` states that the module's bytes decode to the module.  The compilation
also passes each function's typed body to `Verified.WGSL.compile`, which returns a WGSL compute
kernel with proofs of its translation and uses the shared WGSL translation, which normalizes
arithmetic NaNs to `0x7fc00000`.  [The native dispatch theorems](VerifiedDispatch.lean)
combine `Compiled.dispatch_value` with each generated denotation equation `compiled.f.denote_eq`,
so that a dispatch of each kernel computes its Lean function.  [The kernel
map](VerifiedKernels.lean) names the kernel of each host call, and [the host
instance](VerifiedHost.lean) gathers their dispatch theorems into `backend`, a `KernelBackend`.
[The verified compiler manual](../../docs/verified-manual.md#wgsl-kernels) gives the subset that
the translation accepts and the conditions of its dispatch theorem.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, `compiled.f.trapFree` | For each compiled function `f`, `gpt32.wasm` computes `f` bit for bit, unless the call stops at `unreachable`, and without that stop under room for `top` to rise by `compiled.f.bound` within the memory cap. |
| `compiled.bytes` | `encode` succeeds on `compiled.module`, `decode` reads the bytes back as the module, and the module implements every compiled function. |
| `gpt32_file`, `gpt32_file_decode` | `build/verified/gpt32.wasm` holds `encode compiled.module` and decodes to `compiled.module`.  [`File.lean`](File.lean) checks both after the file is written. |
| `embedKernel_dispatch` and the other dispatch theorems | Under bounds below `2^29` on the input sizes and the output count, with an output buffer that has the length header and room for every element, and with enough invocations to cover the output, a dispatch of each kernel leaves its Lean function of the inputs in the output buffer and is race-free. |
| `Demos.Gpt32.generate_host` | For the kernels of a backend, under bounds on the shape and the tokens, for weights loaded from the files and a prompt of fewer than 1,024 tokens, the commands of `setupItems`, the steps of the prompt, and one more step run without error and race-free, and leave the scores of `step32` for the last token in the output buffers. |
| `Demos.Gpt32.Verified.generate_host` | `Demos.Gpt32.generate_host` for `backend`, whose kernels are those of the verified compilation. |

## The host theorem and the device model

`Demos.Gpt32.generate_host` holds for the kernels of any `KernelBackend`, which gives a kernel for
each host call with the call's dispatch theorem.  It composes those theorems with
[`Exec.lean`](Exec.lean), which gives meaning to the typed items of the host program and to their
host commands and shows that a run of the items is a run of their commands, and with
[`Compose.lean`](Compose.lean), which follows the eighteen kernel calls of a layer.
`Demos.Gpt32.Verified.generate_host` instantiates it with `backend`, so the commands, run with the
verified kernels, leave the bits of `step32`, the Lean step, in the score buffers, and every
dispatch is race-free.

The theorems prove successful execution and race freedom in a device model with strict binary32
arithmetic, under their shape, buffer, and token bounds.  A GPU may flush subnormal values and fuse
multiply-adds, as the WGSL specification permits.  On an Apple GPU, the LeanExe compiler's kernels
of the same functions, before the shared translation normalized arithmetic NaNs, gave scores that
differed from those of their Wasm module by up to 5.2e-5 of the largest score, while greedy
generation chose the same token at all 32 steps.  [The design document](../../docs/design.md#gpu)
states what the device model adds to the trusted base, and [the description of the
pages](../../tests/web/README.md) states what is proved about the browser page.  The host
processes, file I/O, and browser remain outside the proofs.

## Building, running, and testing

```sh
tools/leanrun --timeout 20m lake build Demos.Gpt32.VerifiedHost
tools/build-webgpu-host.sh
tests/verified/run.sh --cases gpt32
tests/wgsl/run.sh
tests/gpt32/native.sh
uv run tests/gpt32/generate.py --tokens 8 "The meaning of life is"
uv run tests/web/serve.py
```

The commands build the proofs and the WebGPU host, test the module and the kernels, generate text,
and serve the browser pages, with the setup of [the repository README](../../README.md#commands).
`tests/verified/run.sh --cases gpt32` writes the module and compares it with native Lean on the
Wasm cases of [the checked kernel corpus](VerifiedCases.lean), and without `--cases` the driver also
checks `File.lean` against the file it wrote.  The corpus covers empty and short arrays, signed
zeros, subnormals, infinities, and NaNs, and its Wasm cases also check allocations and retained
blocks.  `tests/wgsl/run.sh` runs the kernels, with the binary32 example's verified kernels, on the
cases of [`tests/wgsl/Cases.lean`](../../tests/wgsl/Cases.lean) and of the corpus on the
SwiftShader and llvmpipe Vulkan drivers, and compares each output word with native Lean's.

[`tests/gpt32/native.sh`](../../tests/gpt32/native.sh) runs small random models through `generate`
of [`Driver.lean`](Driver.lean), the driver that [`Generate.lean`](Generate.lean) runs, on the
verified `gpt32.wasm` and on both Vulkan drivers, and compares every score bit and each greedy
token with native `step32`.  Its Wasm session adapter,
[`tools/gpt32-wasm-host.mjs`](../../tools/gpt32-wasm-host.mjs), uses the Wasm host of the browser
page, [`hosts.js`](../../tests/gpt32/browser/hosts.js).
[`tests/gpt32/generate.py`](../../tests/gpt32/generate.py) writes the pinned checkpoint's weights
to `build/gpt2-32/`, 949 MiB, and generates text greedily with the kernels, which `Generate.lean`
writes to `build/wgsl`.  For each step it reports the largest score difference from Hugging Face's
float32 model, relative to the largest score, and whether the two models choose the same token.
The script has not run with these kernels.  `tests/web/serve.py` serves the kernels,
`build/verified/gpt32.wasm`, and the verified sampler module `build/verified/gpt.wasm` to the
browser pages.

## Related examples

[`Gpt`](../Gpt/README.md) is the same model in binary64 on WebAssembly, with theorems about the
bytes, and the GPT-2 browser page samples tokens with its `sampleTopK`.
[`Binary32`](../../Examples/Binary32/README.md) has the verified WGSL kernels of `scale32`,
`axpyArray32`, `matVec32`, and `condMix32`, which `tests/wgsl/run.sh` runs with this demo's
kernels.  The LTG entry [`wgsl-kernel`](../../ltg/entries/wgsl-kernel/README.md) describes the
printer, the parser, and the dispatch semantics of the WGSL library.

## References

- A. Radford, J. Wu, R. Child, D. Luan, D. Amodei, and I. Sutskever, "Language Models are
  Unsupervised Multitask Learners," OpenAI, 2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/),
  [§15.7.2](https://www.w3.org/TR/WGSL/#differences-from-ieee754) and
  [§15.7.5](https://www.w3.org/TR/WGSL/#reassociation-and-fusion).
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/).
- gfx-rs, [wgpu-native](https://github.com/gfx-rs/wgpu-native).
