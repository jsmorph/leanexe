# Remove the first zero

## Request, specification, and program

[The request](request.txt) asks for an array of at most eight words without its first zero, with the
other words in order, for the input itself when it has no zero, and for the empty array when the
input is longer.  [The specification](Spec.lean) states that behavior with `Array.findIdx?` and
`Array.eraseIdx!`.  The verified compiler reads neither `Array.findIdx?`, which returns an `Option`, nor
`Array.eraseIdx!`, so [the program](Program.lean) computes the same array another way.  `firstZero`
is a loop over the first `count` words that keeps the index of the first zero, or `count` when there
is none, and `compute` builds the result by copying the words before that index and shifting the
rest down by one.  The command `verified_compile compiled := [firstZero, compute]` in [the verified
compilation](Compiled.lean) compiles both functions into a 1,882-byte module.

## The bytes remove the first zero

| Theorem | Statement |
|---------|-----------|
| `firstZero_cases` | `firstZero` gives `count` when the first `count` words hold no zero, and otherwise the index of the first zero. |
| `compute_eq` | `compute` equals `expected` on every array of fewer than 2^64 words. |
| `compute_bound` | `compiled.compute.bound xs` is at most 120 bytes. |
| `removeZero_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 120 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 120 bytes. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `removeZero_file`, `removeZero_file_decode` | `build/verified/removeZero.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

The general prefix search `firstZero` belongs to [the array-search
library](../../Library/Arrays/README.md), and its first-match theorem `firstZero_cases` is in [the
array-search proof](../../Library/Arrays/Search/Proof.lean).  `compute_eq` is in [the proof of the
specification](Proof.lean), and `compute_bound` and `removeZero_call` are in [the verified
compilation](Compiled.lean).  The theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
`compute_eq` connects the loop to `Array.findIdx?` and the build to `Array.eraseIdx!` through the
core lemmas `Array.findIdx?_eq_some_iff_getElem` and `Array.getElem_eraseIdx`.

`verified_compile` generates `compiled.compute.trapFree`, which states that function 3 computes
`compute` without a trap from a store in which `top` can rise by `compiled.compute.bound xs` bytes,
and `compiled.compute.bound_eq`, which gives that bound as one block of the result's length.
`compute_bound` closes the bound to 120 bytes, and `removeZero_call` composes the trap-free theorem
with `compute_eq` through `arrayCall` of [the shared call theorem](../ArrayCall.lean).  The
generated `compiled.firstZero.implements` states that function 2 computes the library's `firstZero`
without a trap, since the loop allocates nothing.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.RemoveZero.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.RemoveZero.Compiled Examples.RemoveZero.compiled.module build/verified/removeZero.wasm
build/tools/leanexe-wasmtime-host call build/verified/removeZero.wasm compute array-u64 \
  array-u64:7,0,9,0
tests/verified/run.sh --cases removeZero
tests/native/verified.sh --module removeZero
```

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  The call
prints `[7, 9, 0]`.  [The verified driver](../../tests/verified/run.sh) runs `compute` on the inputs
of [`Cases.lean`](Cases.lean) against `expected`, and `firstZero` on each input with three counts,
in Wasmtime with the allocation counters.  The inputs include the empty array, arrays of zeros, a
zero first and last, and nine words.  [The native driver](../../tests/native/verified.sh) runs the
same cases on the module's translation to C, compiled with CompCert.

## Related examples

[`Increment`](../Increment/README.md) builds its result in the same way and states its call theorem,
`increment_call`, through `arrayCall` as well.  [`Updates`](../Updates/README.md) removes an element
with `eraseIdxIfInBounds`, in place when the array is owned.  The VKB entry
[`loop-combinators`](../../VKB/entries/loop-combinators/README.md) holds the lemmas about
`LeanExe.build` that `compute_eq` uses.

## References

- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
- [Verified Compiler Manual: Restrictions](../../docs/verified-manual.md#restrictions).
