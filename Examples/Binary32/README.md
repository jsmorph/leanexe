# Binary32: `Float32` in WebAssembly and WGSL

## What it is

[The program](Program.lean) has eight functions on Lean's `Float32`, IEEE 754 binary32: scalar
`axpy32`, `hypot32`, `ratio32`, and `piecewise32`; the array functions `scale32`, `axpyArray32`, and
`matVec32`, each a `LeanExe.build`; and `condMix32`, a build with nested conditionals and an index
computed from the element's position.  [The module definition](Module.lean) compiles all eight into
the 2,738-byte `binary32.wasm`.  [`Wgsl.lean`](Wgsl.lean) translates the compiled IR of `scale32`,
`axpyArray32`, `matVec32`, and `condMix32` into WGSL compute kernels for a GPU.

## What it shows

The WebAssembly theorems use ProofKit's binary32 chain, which proves that Lean's `Float32` addition,
subtraction, multiplication, division, and square root equal Talos's `IEEE32` functions for all
inputs, with comparison and sign lemmas for `piecewise32`.  The WGSL translation reads a build out
of the IR and emits one kernel invocation per element.  Each kernel has three theorems: the
translation succeeds, the parser reads the printed text back as the kernel, and a dispatch over at
least as many invocations as elements writes the Lean function's result into the output buffer, with
distinct invocations storing to distinct words.  The dispatch theorems hold under a device model
with strict binary32 arithmetic, race-free dispatch, and no dynamic errors.

| Theorem | Statement |
|---------|-----------|
| `axpy32_implements` … `axpyArray32_implements` | Each of functions 2 to 8 of `binary32.module` implements its Lean function bit for bit. |
| `binary32_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements those seven functions. |
| `scaleKernel_dispatch`, `axpyArrayKernel_dispatch`, `matVecKernel_dispatch`, `condMixKernel_dispatch` | A dispatch of the kernel computes the Lean function into the output buffer and is race-free. |
| `scaleKernel_text` and its siblings | `Module.parse` of the printed kernel gives the kernel back. |

The proofs are in [`Verify.lean`](Verify.lean) and [`Wgsl.lean`](Wgsl.lean), and they use only the
axioms `propext`, `Classical.choice`, and `Quot.sound`.  `condMix32` has a WGSL theorem and no
WebAssembly theorem.  [The manual](../../docs/manual.md#wgsl-kernels-and-the-browser-pages)
describes the WGSL path, and [the design document](../../docs/design.md#gpu) states what the device
model adds to the trusted base.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Binary32.Verify Examples.Binary32.Wgsl
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Binary32.Module Examples.Binary32.binary32.module build/binary32/binary32.wasm
build/tools/leanexe-wasmtime-host call build/binary32/binary32.wasm axpy32 f32 \
  f32:1073741824 f32:1077936128 f32:1065353216
tools/leanrun --timeout 10m lake env lean --run tools/EmitWgsl.lean \
  Examples.Binary32.Wgsl Examples.Binary32.scaleKernel build/wgsl/scale.wgsl
tests/wgsl/run.sh
```

The commands build the proofs, write the module, call it in the Wasmtime host, print one kernel, and
run the kernel tests, with the setup of [the repository README](../../README.md#commands).  The call
computes `2 * 3 + 1` from the binary32 bits of 2, 3, and 1 and prints 1088421888, the bits of 7.0.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 388 cases of
[`Cases.lean`](Cases.lean) with native Lean.  [`tests/wgsl/run.sh`](../../tests/wgsl/run.sh) runs
the kernel cases on the SwiftShader and llvmpipe Vulkan drivers through `leanexe-webgpu-host`, which
[`tools/build-webgpu-host.sh`](../../tools/build-webgpu-host.sh) builds, and `uv run
tests/web/serve.py` serves a page that runs them on a browser's WebGPU.

## Related examples

[`Axpy`](../Axpy/README.md), [`ScaledHypot`](../ScaledHypot/README.md), and
[`Piecewise`](../Piecewise/README.md) are the binary64 forms of the scalar functions.
[`Gpt32`](../Gpt32/README.md) applies the same translation to the kernels of GPT-2 in binary32.  The
LTG entries [`binary32-arithmetic`](../../ltg/entries/binary32-arithmetic/README.md) and
[`wgsl-kernel`](../../ltg/entries/wgsl-kernel/README.md) describe the rules.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/), the language of the kernels.
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/), the API that dispatches them.
- [The description of the browser pages](../../tests/web/README.md).
