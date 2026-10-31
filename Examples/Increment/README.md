# Increment: each element plus one

## Request, specification, and program

[The request](request.txt) asks for each element of an array of at most eight words plus one, with
wrapping arithmetic, and for the empty array when the input is longer.  [The
specification](Spec.lean) states that behavior in ordinary Lean, with `Array.map`.  [The
program](Program.lean) sets the count to the input's size when it is at most eight and to 0
otherwise, and builds that many words, each the input's word plus one, so one build serves both
cases.  `verified_compile compiled := [compute]` in [the verified compilation](Compiled.lean)
compiles the definition into a 1,605-byte module that exports `compute`.

## The module computes the increment

`verified_compile` generates `compiled.compute.trapFree`, which states that function 2 computes
`compute` without a trap from a store in which `top` can rise by `compiled.compute.bound xs` bytes,
and `compiled.compute.bound_eq`, which gives that bound as one block of the result's length.
`compute_bound` closes the bound to 120 bytes, and `increment_call` composes the trap-free theorem
with `compute_eq` through `arrayCall` of [the shared call theorem](../ArrayCall.lean).
`compute_callSpec` states the call as an instance of `Verified.CallSpec`, with the generated bound
as the room, and the generated `compiled.compute.native` states the same computation for the C
function of the module's translation.

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | `compute` equals `expected` on every array of fewer than 2^64 words. |
| `compute_bound` | `compiled.compute.bound xs` is at most 120 bytes. |
| `increment_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 120 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 120 bytes. |
| `compute_callSpec` | Called with a borrowed array `xs` from a ready store in which `top` can rise by `compiled.compute.bound xs` bytes, the export `compute` returns without a trap an owned array that holds `expected xs`, leaves a ready store, and raises `top` by at most that bound. |
| `increment_file`, `increment_file_decode` | `build/verified/increment.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

`compute_eq`, in [the proof of the specification](Proof.lean), splits on whether the input has at
most eight words and, for such an input, compares the build with `Array.map` element by element.
A ready store has the allocator invariant, a memory cap of at most 65,535 pages, and the program's
tables at their addresses, and `Verified.Ready.initial` proves that the store in which the module
starts is ready.  `increment_call` and `compute_callSpec` use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Building, running, and testing

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

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository README](../../README.md#commands).
The call prints `[1, 42, 0]`: the last word wraps.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean), among them the
empty array, arrays of eight and nine words, and words that wrap, in Wasmtime against `expected`
with the allocation counters.  [The native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert, and takes CompCert's `ccomp`, `clightgen`, and
runtime directory as its header describes.

## Related examples

[`RemoveZero`](../RemoveZero/README.md) also builds its result with `LeanExe.build`.
[`Euler`](../../Demos/Euler/README.md) and [`Drone`](../../Demos/Drone/README.md) have verified
call theorems, `euler_solve_call` and `drone_compute_call`, which state the room that
`increment_call` takes as a memory cap in pages.  The LTG entry
[`array-build`](../../ltg/entries/array-build/README.md) holds proof guidance for `LeanExe.build`.

## References

- [Verified Compiler Manual: Bounds and total
  execution](../../docs/verified-manual.md#bounds-and-total-execution).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
