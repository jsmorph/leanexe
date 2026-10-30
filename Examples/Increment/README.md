# Increment: each element plus one

## Request, specification, and program

[The request](request.txt) asks for each element of an array of at most eight words plus one, with
wrapping arithmetic, and for the empty array when the input is longer.  [The
specification](Spec.lean) states that behavior in ordinary Lean, with `Array.map`.  [The
program](Program.lean) sets the count to the input's size when it is at most eight and to 0
otherwise, and builds that many words, each the input's word plus one.  One build serves both cases,
because the dialect places builds at the top of a function rather than in a branch.  [The module
definition](Module.lean) compiles it into a 1,524-byte `increment.wasm` that exports `compute`, and [the
verified compilation](Compiled.lean) compiles the same definition with the verified compiler into a
1,605-byte module.

## The bytes compute the increment, with total execution

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `increment_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |
| `increment_total` | From an allocator whose `top` leaves 120 bytes within the first 16 pages, with 16 pages and a cap that allows them, the call returns the words of `expected` without stopping at `unreachable` and leaves memory at 16 pages. |

`compute_eq` is in [the proof of the specification](Proof.lean), which the theorems of both
compilers use, and the other theorems are in [the proofs](Verify.lean).  They use only `propext`,
`Classical.choice`, and `Quot.sound`.  The proof of `Implements` applies the rule of the build
template.  With `compute_eq`, `Implements.congr` states it for the specification.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Increment.Verify
mkdir -p build/increment
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Increment.Module Examples.Increment.increment.module build/increment/increment.wasm
build/tools/leanexe-wasmtime-host call build/increment/increment.wasm compute array-u64 \
  array-u64:0,41,18446744073709551615
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[1, 42, 0]`: the last word
wraps.  [The module tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run the
request's samples and edge cases in Wasmtime against `expected`.

## The verified compiler's module

`verified_compile compiled := [compute]` in [the verified compilation](Compiled.lean) generates
`compiled.compute.trapFree`, which states that function 2 computes `compute` without a trap from a
store in which `top` can rise by `compiled.compute.bound xs` bytes, and `compiled.compute.bound_eq`,
which gives that bound as one block of the result's length.  `compute_bound` closes the bound to 120
bytes, and `increment_call` composes the trap-free theorem with `compute_eq` through `arrayCall` of
[the shared call theorem](../ArrayCall.lean).  The generated `compiled.compute.native` states the
same computation for the C function of the module's translation.

| Theorem | Statement |
|---------|-----------|
| `compute_bound` | The allocation bound of `compute` is at most 120 bytes. |
| `increment_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 120 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 120 bytes. |

`increment_call` and `increment_total` both exclude the trap, under different memory premises.
`increment_total` requires 16 pages of memory with `top` at least 120 bytes below their end and
concludes that the memory stays at 16 pages.  `increment_call` requires room for 120 bytes within
the memory cap and allows the memory to grow within it.

```sh
tools/leanrun --timeout 60m lake build Examples.Increment.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Increment.Compiled Examples.Increment.compiled.module build/verified/increment.wasm
build/tools/leanexe-wasmtime-host call build/verified/increment.wasm compute array-u64 \
  array-u64:0,41,18446744073709551615
tests/verified/run.sh --cases increment
tests/native/verified.sh --module increment
```

The call prints `[1, 42, 0]`, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against `expected` with the allocation counters, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  The native driver takes CompCert's `ccomp`, `clightgen`, and runtime directory as its
header describes.

## Related examples

[`RemoveZero`](../RemoveZero/README.md) also builds its result with `LeanExe.build`.
[`Euler`](../../Demos/Euler/README.md) and [`Drone`](../../Demos/Drone/README.md) have complete-execution theorems
with memory bounds of the same form as `increment_total`.  The LTG entry
[`array-build`](../../ltg/entries/array-build/README.md) describes the build template.

## References

- [LeanExe Compiler Manual: Total execution and memory
  bounds](../../docs/leanexe-manual.md#total-execution-and-memory-bounds).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
