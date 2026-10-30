# Binary32: `Float32` in WebAssembly and WGSL

## Eight `Float32` functions and four GPU kernels

[The program](Program.lean) has eight functions on Lean's `Float32`, IEEE 754 binary32: scalar
`axpy32`, `hypot32`, `ratio32`, and `piecewise32`; the array functions `scale32`, `axpyArray32`, and
`matVec32`, each a `LeanExe.build`; and `condMix32`, a build with nested conditionals and an index
computed from the element's position.  [The module definition](Module.lean) compiles all eight into
the 2,738-byte `binary32.wasm`, and [the verified compilation](Compiled.lean) compiles all eight
with the verified compiler into a 3,258-byte module.  [`Wgsl.lean`](Wgsl.lean) translates the
compiled IR of `scale32`, `axpyArray32`, `matVec32`, and `condMix32` into WGSL compute kernels for a
GPU.

The reusable scaling, AXPY, and matrix-vector definitions come from [the linear-algebra library](../../Library/Numerics/LinearAlgebra/README.md).  This example retains the scalar and conditional kernels and their Wasm and WGSL proofs.

## Binary32 equality and kernel theorems

The WebAssembly theorems use ProofKit's binary32 chain, which proves that Lean's `Float32` addition,
subtraction, multiplication, division, and square root equal Talos's `IEEE32` functions for all
inputs, with comparison and sign lemmas for `piecewise32`.  The WGSL translation reads a build out
of the IR and emits one kernel invocation per element.  Each kernel has three theorems: the
translation succeeds, the parser reads the printed text back as the kernel, and a dispatch over at
least as many invocations as elements writes the Lean function's result into the output buffer, with
distinct invocations storing to distinct words.  The dispatch theorems hold under a device model
with strict binary32 arithmetic.  They prove successful modeled execution and race freedom under
their buffer and invocation bounds.

| Theorem | Statement |
|---------|-----------|
| `axpy32_implements` … `axpyArray32_implements` | Each of functions 2 to 8 of `binary32.module` implements its Lean function bit for bit. |
| `binary32_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements those seven functions. |
| `scaleKernel_dispatch`, `axpyArrayKernel_dispatch`, `matVecKernel_dispatch`, `condMixKernel_dispatch` | A dispatch of the kernel computes the Lean function into the output buffer and is race-free. |
| `scaleKernel_text` and its siblings | `Module.parse` of the printed kernel gives the kernel back. |

The proofs are in [`Verify.lean`](Verify.lean) and [`Wgsl.lean`](Wgsl.lean), and they use only the
axioms `propext`, `Classical.choice`, and `Quot.sound`.  `condMix32` has a WGSL theorem and no
WebAssembly theorem.  [The LeanExe compiler
manual](../../docs/leanexe-manual.md#wgsl-kernels-and-the-browser-pages) describes the WGSL path,
and [the design document](../../docs/design.md#gpu) states what the device model adds to the trusted
base.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Binary32.Verify Examples.Binary32.Wgsl
mkdir -p build/binary32
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Binary32.Module Examples.Binary32.binary32.module build/binary32/binary32.wasm
build/tools/leanexe-wasmtime-host call build/binary32/binary32.wasm axpy32 f32 \
  f32:1073741824 f32:1077936128 f32:1065353216
mkdir -p build/wgsl
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

## The verified compiler's module

`verified_compile compiled := [axpy32, hypot32, ratio32, matVec32, piecewise32, scale32,
axpyArray32, condMix32]` in [the verified compilation](Compiled.lean) compiles the eight functions
in the order of the LeanExe module, so functions 2 to 9 are the same functions in both modules.
`compiled.bytes` states that the module's bytes decode to the module, whose functions compute the
eight Lean definitions, and the generated `trapFree` theorems exclude a trap when `top` can rise by
each function's allocation bound.  `Verified.WGSL.compile` translates the reflected bodies of
`scale32`, `axpyArray32`, `matVec32`, and `condMix32` into the kernels `verifiedScale32Kernel`,
`verifiedAxpyArray32Kernel`, `verifiedMatVec32Kernel`, and `verifiedCondMix32Kernel`.

| Theorem | Statement |
|---------|-----------|
| `compiled.bytes` | The module's bytes decode to the module, whose functions 2 to 9 compute `axpy32`, `hypot32`, `ratio32`, `matVec32`, `piecewise32`, `scale32`, `axpyArray32`, and `condMix32`. |
| `scale32_dispatch`, `axpyArray32_dispatch`, `matVec32_dispatch`, `condMix32_dispatch` | A dispatch of the verified kernel computes the Lean function into the output buffer and is race-free, under the premises of the LeanExe compiler's theorem for the same kernel. |

Each dispatch theorem comes from `Verified.WGSL.Compiled.dispatch_value` and the generated
`denote_eq` equation of its function, and each takes the premises of `scaleKernel_dispatch`,
`axpyArrayKernel_dispatch`, `matVecKernel_dispatch`, or `condMixKernel_dispatch`.  The LeanExe
compiler's kernels come from its IR with a specification of the build and an element lemma for
each kernel, and the verified kernels come from one translation with one generic proof.
`binary32_bytes` allows a trap at `unreachable` and covers functions 2 to 8, and the verified
module also covers `condMix32`, whose WebAssembly function has no theorem of the LeanExe compiler.

The reflector reads the condition `i % 4 ≤ 3 ∧ i / 4 * 4 + (3 - i % 4) < n` of `condMix32` as
`decide (i % 4 ≤ 3) && decide (i / 4 * 4 + (3 - i % 4) < n)`, by the rule that [the verified
compiler manual](../../docs/verified-manual.md#array-literals-and-conditions-on-propositions)
describes, and the WGSL translation lowers the conjunction.  `condMix32_dispatch` states for the
verified kernel what `condMixKernel_dispatch` states for the kernel of the LeanExe compiler.  The
WebAssembly cases of `condMix32` come from `condMixArgs` in [`Cases.lean`](Cases.lean), and the
LeanExe module's cases have none.

```sh
tools/leanrun --timeout 60m lake build Examples.Binary32.Compiled
mkdir -p build/verified build/wgsl
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Binary32.Compiled Examples.Binary32.compiled.module build/verified/binary32.wasm
build/tools/leanexe-wasmtime-host call build/verified/binary32.wasm axpy32 f32 \
  f32:1073741824 f32:1077936128 f32:1065353216
tools/leanrun --timeout 10m lake env lean --run tools/EmitWgsl.lean \
  Examples.Binary32.Compiled Examples.Binary32.verifiedCondMix32Kernel \
  build/wgsl/verifiedCondMix32.wgsl
tests/verified/run.sh --cases binary32
tests/native/verified.sh --module binary32
tests/wgsl/run.sh --verified
```

The call prints 1088421888, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the 388 inputs of the LeanExe cases and 56 inputs of
`condMix32` in Wasmtime with the allocation counters, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  `tests/wgsl/run.sh --verified` writes the four verified kernels and the cases of
[`VerifiedGpuCases.lean`](VerifiedGpuCases.lean), which use the same inputs, and runs them on the
SwiftShader and llvmpipe drivers.

## Related examples

[`Axpy`](../Axpy/README.md), [`ScaledHypot`](../ScaledHypot/README.md), and
[`Piecewise`](../Piecewise/README.md) are the binary64 forms of the scalar functions.
[`Gpt32`](../../Demos/Gpt32/README.md) applies the same translation to the kernels of GPT-2 in binary32.  The
LTG entries [`binary32-arithmetic`](../../ltg/entries/binary32-arithmetic/README.md) and
[`wgsl-kernel`](../../ltg/entries/wgsl-kernel/README.md) describe the rules.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/), the language of the kernels.
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/), the API that dispatches them.
- [The description of the browser pages](../../tests/web/README.md).
