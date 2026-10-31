# Binary32: `Float32` in WebAssembly and WGSL

## Eight `Float32` functions and four GPU kernels

[The program](Program.lean) has eight functions on Lean's `Float32`, IEEE 754 binary32: scalar
`axpy32`, `hypot32`, `ratio32`, and `piecewise32`; the array functions `scale32`, `axpyArray32`, and
`matVec32`, each a `LeanExe.build`; and `condMix32`, a build with nested conditionals and an index
computed from the element's position.  The program defines the scalar functions and `condMix32`
and exports `scale32`, `axpyArray32`, and `matVec32` from [the linear-algebra
library](../../Library/Numerics/LinearAlgebra/README.md), which holds the reusable scaling, AXPY,
and matrix-vector definitions.  `verified_compile compiled := [axpy32, hypot32, ratio32, matVec32,
piecewise32, scale32, axpyArray32, condMix32]` in [the verified compilation](Compiled.lean)
compiles all eight into a 3,258-byte module, whose functions 2 to 9 are the eight functions in that
order.  `Verified.WGSL.compile` translates the reflected bodies of `scale32`, `axpyArray32`,
`matVec32`, and `condMix32` into the WGSL compute kernels `verifiedScale32Kernel`,
`verifiedAxpyArray32Kernel`, `verifiedMatVec32Kernel`, and `verifiedCondMix32Kernel` for a GPU.

## Module and kernel theorems

The generated `trapFree` theorems exclude a trap when `top` can rise by each function's allocation
bound.  `Verified.WGSL.compile` returns each kernel with proofs of its translation and local
layout, and each dispatch theorem comes from `Verified.WGSL.Compiled.dispatch_value` and the
generated `denote_eq` equation of its function.  The dispatch theorems hold under a device model
with strict binary32 arithmetic.  They prove successful modeled execution and race freedom under
their buffer and invocation bounds.

| Theorem | Statement |
|---------|-----------|
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and its functions 2 to 9 compute `axpy32`, `hypot32`, `ratio32`, `matVec32`, `piecewise32`, `scale32`, `axpyArray32`, and `condMix32`. |
| `binary32_file`, `binary32_file_decode` | `build/verified/binary32.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |
| `scale32_dispatch`, `axpyArray32_dispatch`, `matVec32_dispatch`, `condMix32_dispatch` | Dispatch of the kernel over at least as many invocations as output elements, with an output buffer of the result's size whose length word the host has written, writes the Lean function's result into the buffer, and distinct invocations store to distinct words, under bounds on the sizes and the invocation count. |

The reflector reads the condition `i % 4 ≤ 3 ∧ i / 4 * 4 + (3 - i % 4) < n` of `condMix32` as
`decide (i % 4 ≤ 3) && decide (i / 4 * 4 + (3 - i % 4) < n)`, by the rule that [the verified
compiler manual](../../docs/verified-manual.md#array-literals-and-conditions-on-propositions)
describes, and the WGSL translation lowers the conjunction.  The theorems use only the axioms
`propext`, `Classical.choice`, and `Quot.sound`.  [The manual's section on WGSL
kernels](../../docs/verified-manual.md#wgsl-kernels) describes the translation and its dispatch
theorem, [its section on the WGSL
library](../../docs/verified-manual.md#the-wgsl-library-and-the-browser-pages) describes the device
model and the browser pages, and [the design document](../../docs/design.md#gpu) states what the
device model adds to the trusted base.

## Building, running, and testing

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
tests/wgsl/run.sh
```

The first commands build the verified compilation and its proofs, write the module, call it in the
Wasmtime host, and print one kernel, with the setup of [the repository
README](../../README.md#commands).  The call computes `2 * 3 + 1` from the binary32 bits of 2, 3,
and 1 and prints 1088421888, the bits of 7.0.  [The verified driver](../../tests/verified/run.sh)
runs, in Wasmtime with the allocation counters, 388 cases of `axpy32`, `hypot32`, `ratio32`,
`piecewise32`, `scale32`, `axpyArray32`, and `matVec32` and 56 cases of `condMix32`, with the
inputs of [`Cases.lean`](Cases.lean).  [The native driver](../../tests/native/verified.sh) runs
them on the module's translation to C, compiled with CompCert.

`tests/wgsl/run.sh --verified` writes the verified kernels and the cases of
[`VerifiedGpuCases.lean`](VerifiedGpuCases.lean), which use the same inputs, and runs them on the
SwiftShader and llvmpipe Vulkan drivers through `leanexe-webgpu-host`, which
[`tools/build-webgpu-host.sh`](../../tools/build-webgpu-host.sh) builds.  Without an option,
`tests/wgsl/run.sh` writes the verified kernels under the names `scale`, `axpyArray`, `matVec`, and
`condMix` and runs them on the cases of [`tests/wgsl/Cases.lean`](../../tests/wgsl/Cases.lean).
The kernel page of `uv run tests/web/serve.py` loads these kernels and runs the cases on a
browser's WebGPU.

## Related examples

[`Axpy`](../Axpy/README.md), [`ScaledHypot`](../ScaledHypot/README.md), and
[`Piecewise`](../Piecewise/README.md) are the binary64 forms of the scalar functions.
[`Gpt32`](../../Demos/Gpt32/README.md) applies the same translation to the kernels of GPT-2 in
binary32.  The VKB entry [`verified-wgsl-kernel`](../../VKB/entries/verified-wgsl-kernel/README.md)
describes how a build compiles to a WGSL kernel and how its dispatch theorem is proved.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
- W3C, [WebGPU Shading Language](https://www.w3.org/TR/WGSL/).
- W3C, [WebGPU](https://www.w3.org/TR/webgpu/).
- [WebGPU Pages](../../tests/web/README.md).
