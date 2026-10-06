# Gpt32: GPT-2 in binary32 on WGSL

## What it is

[The program](Program.lean) is one generation step of GPT-2 124M in Lean `Float32`, binary32,
written for GPU kernels: every array is a build element by element, and the helpers that kernels
share are `@[inline]`, so the compiler unfolds them into each kernel.  Its thirteen kernel
functions, from `expArray32` to `logits32`, are translated from their compiled IR into WGSL compute
kernels.  [The host program](HostProgram.lean) is the list of commands that runs a step on
`leanexe-webgpu-host`: buffer loads, word and float constants, and kernel dispatches.  [The module
definition](Module.lean) also compiles the thirteen functions into the 6,384-byte `gpt32.wasm`,
which the browser page runs on the CPU for comparison.

## What it shows

`generate_host` states that the host's commands, run from the loaded weights for a prompt and one
more token, end with the scores of `step32`, the Lean step, in the output buffers, and that every
dispatch along the way is race-free.  It composes the dispatch theorem of each kernel in
[`Proofs.lean`](Proofs.lean) and [`Kernels.lean`](Kernels.lean) with [`Exec.lean`](Exec.lean), which
gives the commands their meaning, and [`Compose.lean`](Compose.lean), which follows the eighteen
kernel calls of a layer.  The theorems hold under a device model with strict binary32 arithmetic,
race-free dispatch, and no dynamic errors.  A GPU may flush subnormal values and fuse multiply-adds,
as the WGSL specification permits.  In headless Chromium with SwiftShader, the kernels' scores
equaled those of `gpt32.wasm` bit for bit at all 16 steps of one run, and on an Apple GPU they
differed by up to 5.2e-5 of the largest score, while greedy generation chose the same token at all
32 steps.

| Theorem | Statement |
|---------|-----------|
| `generate_host` | Under bounds on the shape and the tokens, for weights loaded from the files and a prompt of fewer than 1,024 tokens, the commands of `setupItems`, the steps of the prompt, and one more step run without error and race-free, and leave the scores of `step32` for the last token in the output buffers. |
| `layerNormKernel_dispatch` and the other dispatch theorems | A dispatch of each kernel computes its Lean function into the output buffer and is race-free. |
| `layerNormSpec_module` and its siblings | The translation of each kernel's IR succeeds and gives the kernel. |

The proofs are in [`Proofs.lean`](Proofs.lean), [`Kernels.lean`](Kernels.lean),
[`Exec.lean`](Exec.lean), and [`Compose.lean`](Compose.lean), and they use only the axioms
`propext`, `Classical.choice`, and `Quot.sound`.  `gpt32.wasm` has no WebAssembly theorem.  [The
design document](../../docs/design.md#gpu) states what the device model adds to the trusted base,
and [the description of the pages](../../tests/web/README.md) states what is proved about the
browser page.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Gpt32.Compose
tools/build-webgpu-host.sh
tests/wgsl/run.sh
tests/gpt32/native.sh
uv run tests/gpt32/generate.py --tokens 8 "The meaning of life is"
uv run tests/web/serve.py
```

The commands build the proofs and the WebGPU host, run the kernel tests and the step comparison,
generate text, and serve the browser pages, with the setup of [the repository
README](../../README.md#commands).  [`tests/wgsl/run.sh`](../../tests/wgsl/run.sh) runs the kernel
cases on the SwiftShader and llvmpipe Vulkan drivers, and
[`tests/gpt32/native.sh`](../../tests/gpt32/native.sh) runs small random models through
[`Generate.lean`](Generate.lean) on both drivers and compares each step's scores with native Lean's
`step32`.  [`tests/gpt32/generate.py`](../../tests/gpt32/generate.py) writes the pinned checkpoint's
weights to `build/gpt2-32/`, 949 MiB, generates with the kernels, and compares each step with
Hugging Face's float32 model.  The command above printed "The meaning of life is not the same as the
meaning of death" in 10.6 seconds on llvmpipe, with a largest relative score difference of 1.47e-6
and the same token as Hugging Face's model at every step.
[`tests/web/serve.py`](../../tests/web/serve.py) serves the kernel test page and the GPT-2 page on
http://127.0.0.1:8000/.

## Related examples

[`Gpt`](../Gpt/README.md) is the same model in binary64 on WebAssembly, with theorems about the
bytes.  [`Binary32`](../Binary32/README.md) has the first WGSL kernels, `scale32`, `axpyArray32`,
`matVec32`, and `condMix32`.  The LTG entries
[`wgsl-kernel`](../../ltg/entries/wgsl-kernel/README.md) and
[`binary32-arithmetic`](../../ltg/entries/binary32-arithmetic/README.md) describe the rules.

## References

- A. Radford, J. Wu, R. Child, D. Luan, D. Amodei, and I. Sutskever, "Language Models are
  Unsupervised Multitask Learners," OpenAI, 2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/), in particular
  [§15.7.2](https://www.w3.org/TR/WGSL/#differences-from-ieee754) on flushing and
  [§15.7.5](https://www.w3.org/TR/WGSL/#reassociation-and-fusion) on fusion.
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/).
- [wgpu-native](https://github.com/gfx-rs/wgpu-native), which the host uses.
