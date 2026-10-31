# Gpt32: GPT-2 in binary32 on WGSL

## One GPT-2 step as WGSL kernels

[The program](Program.lean) is one generation step of GPT-2 124M in Lean `Float32`, binary32,
written for GPU kernels: every array is a build element by element, and the helpers that kernels
share are `@[inline]`, so the compiler unfolds them into each kernel.  Its thirteen kernel
functions, from `expArray32` to `logits32`, are translated from their compiled IR into WGSL compute
kernels.  [The host program](HostProgram.lean) is the list of commands that runs a step on
`leanexe-webgpu-host`: buffer loads, word and float constants, and kernel dispatches.  [The module
definition](Module.lean) also compiles the thirteen functions into the 6,384-byte `gpt32.wasm`.

Vector addition and the biased linear transform come from [the binary32 linear-algebra library](../../Library/Numerics/LinearAlgebra/README.md).  The demo retains the model-specific kernels and host program.

## The host theorem and device measurements

`generate_host` states that the host's commands, run with the kernels of a `KernelBackend` from
the loaded weights for a prompt and one more token, end with the scores of `step32`, the Lean
step, in the output buffers, and that every dispatch along the way is race-free.  A backend gives
a kernel for each host call with the call's dispatch theorem, and `generate_host` composes those
theorems with [`Exec.lean`](Exec.lean), which gives the commands their meaning, and
[`Compose.lean`](Compose.lean), which follows the eighteen kernel calls of a layer.  [The host
instance](VerifiedHost.lean) supplies the verified compiler's kernels, as [the section on the
verified compiler](#verified-compiler) describes, and no host theorem composes the dispatch
theorems of the LeanExe kernels in [`Proofs.lean`](Proofs.lean) and [`Kernels.lean`](Kernels.lean).
The theorems prove successful execution and race freedom in a device
model with strict binary32 arithmetic, under their shape, buffer, and token bounds.
A GPU may flush subnormal values and fuse multiply-adds,
as the WGSL specification permits.  Before arithmetic-NaN normalization, the kernels' scores in
headless Chromium with SwiftShader equaled those of `gpt32.wasm` bit for bit at all 16 steps of
one run, and on an Apple GPU they
differed by up to 5.2e-5 of the largest score, while greedy generation chose the same token at all
32 steps.

| Theorem | Statement |
|---------|-----------|
| `generate_host` | For the kernels of a backend, under bounds on the shape and the tokens, for weights loaded from the files and a prompt of fewer than 1,024 tokens, the commands of `setupItems`, the steps of the prompt, and one more step run without error and race-free, and leave the scores of `step32` for the last token in the output buffers. |
| `layerNormKernel_dispatch` and the other dispatch theorems | A dispatch of each LeanExe kernel computes its Lean function into the output buffer and is race-free. |
| `layerNormSpec_module` and its siblings | The translation of each kernel's IR succeeds and gives the kernel. |

The proofs are in [`Proofs.lean`](Proofs.lean), [`Kernels.lean`](Kernels.lean),
[`Exec.lean`](Exec.lean), and [`Compose.lean`](Compose.lean), and they use only the axioms
`propext`, `Classical.choice`, and `Quot.sound`.  `gpt32.wasm` has no WebAssembly theorem.  [The
design document](../../docs/design.md#gpu) states what the device model adds to the trusted base,
and [the description of the pages](../../tests/web/README.md) states what is proved about the
browser page.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.Gpt32.Proofs
tools/build-webgpu-host.sh
```

The commands build the proofs of the LeanExe kernels and the WebGPU host, with the setup of [the
repository README](../../README.md#commands).  No driver or page runs the LeanExe kernels or this
`gpt32.wasm`, and [the section on the verified compiler](#verified-compiler) gives the drivers and
pages of the verified kernels.

## Verified compiler

[The Verified compilation](Verified.lean) compiles the same thirteen
functions to Wasm and passes their typed source bodies to the proved WGSL compiler.
`compiled.f.implements`, `compiled.f.trapFree`, and `compiled.f.bound_eq` state execution,
trap-free execution under the allocation bound, and that bound for each function `f`.
`compiled.bytes` connects the encoding to the module.  The driver emits that module as
`build/verified/gpt32.wasm`.  The original compiler's `build/gpt32/gpt32.wasm`, described
above, remains a separate module.

[The native dispatch theorems](VerifiedDispatch.lean) reuse the generic
source theorem and each generated denotation equation.  The thirteen kernels share the
IR-to-WGSL translation, including its NaN normalization.  [The host
instance](VerifiedHost.lean) supplies the twelve generation kernels to
the existing item and layer proofs.  `Demos.Gpt32.Verified.generate_host` instantiates
`generate_host` with these kernels: the commands return the native step's scores, and each
dispatch is race-free, under its device model, loaded-weight conditions, and bounds.  The host processes,
file I/O, and browser remain outside those proofs.

```sh
tools/leanrun --timeout 20m lake build Demos.Gpt32.VerifiedHost
tests/verified/run.sh --cases gpt32
tests/wgsl/run.sh
tests/gpt32/native.sh
uv run tests/gpt32/generate.py --tokens 8 "The meaning of life is"
uv run tests/web/serve.py
```

[The checked kernel corpus](VerifiedCases.lean) compares Wasm and GPU
results with native Lean, including empty and short arrays, signed zeros, subnormals,
infinities, and NaNs.  The Wasm cases also check allocations and retained blocks.
[`tests/gpt32/native.sh`](../../tests/gpt32/native.sh) runs three random models through the driver
of [`Generate.lean`](Generate.lean) in Wasm and on both GPU drivers, comparing every score bit and
each greedy token with native `step32`.  Its Wasm session adapter uses [the browser's existing Wasm
host](../../tests/gpt32/browser/hosts.js).  [`tests/gpt32/generate.py`](../../tests/gpt32/generate.py)
writes the pinned checkpoint's weights to `build/gpt2-32/`, 949 MiB, generates with these kernels,
which `Generate.lean` writes to `build/wgsl`, and compares each step with Hugging Face's float32
model.  With the LeanExe compiler's kernels, the command above printed "The meaning of life is not
the same as the meaning of death" in 10.6 seconds on llvmpipe, with a largest relative score
difference of 1.47e-6 and the same token as Hugging Face's model at every step.  The script has
not run with the verified kernels.  `tests/wgsl/run.sh`
runs these kernels, with the binary32 example's verified kernels, on the cases of
[`tests/wgsl/Cases.lean`](../../tests/wgsl/Cases.lean) and of this corpus, and
`tests/web/serve.py` serves them, `build/verified/gpt32.wasm`, and the verified sampler module
`build/verified/gpt.wasm` to the browser pages.

## Related examples

[`Gpt`](../Gpt/README.md) is the same model in binary64 on WebAssembly, with theorems about the
bytes.  [`Binary32`](../../Examples/Binary32/README.md) has the first WGSL kernels, `scale32`, `axpyArray32`,
`matVec32`, and `condMix32`.  The LTG entries
[`wgsl-kernel`](../../ltg/entries/wgsl-kernel/README.md) and
[`binary32-arithmetic`](../../ltg/entries/binary32-arithmetic/README.md) describe the rules.

## References

- A. Radford, J. Wu, R. Child, D. Luan, D. Amodei, and I. Sutskever, "Language Models are
  Unsupervised Multitask Learners," OpenAI, 2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/),
  [§15.7.2](https://www.w3.org/TR/WGSL/#differences-from-ieee754) and
  [§15.7.5](https://www.w3.org/TR/WGSL/#reassociation-and-fusion).
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/).
- gfx-rs, [wgpu-native](https://github.com/gfx-rs/wgpu-native).
