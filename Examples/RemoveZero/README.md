# Remove the first zero

## Request, specification, and program

[The request](request.txt) asks for an array of at most eight words without its first zero, with the
other words in order, for the input itself when it has no zero, and for the empty array when the
input is longer.  [The specification](Spec.lean) states that behavior with `Array.findIdx?` and
`Array.eraseIdx!`.  The dialect compiles neither `Array.findIdx?`, which returns an `Option`, nor
`Array.eraseIdx!`, so [the program](Program.lean) computes the same array another way.  `firstZero`
is a loop over the first `count` words that keeps the index of the first zero, or `count` when there
is none, and `compute` builds the result by copying the words before that index and shifting the
rest down by one.  [The module definition](Module.lean) compiles both functions into a 1,742-byte
`removeZero.wasm` that exports `firstZero` and `compute`, and [the verified
compilation](Compiled.lean) compiles the same definitions with the verified compiler into a
1,882-byte module.

The general prefix search and its first-match proof live in [the array-search library](../../Library/Arrays/README.md).  The bounded removal specification and its compilation proof remain here.

## The bytes remove the first zero

| Theorem | Statement |
|---------|-----------|
| `firstZero_cases` | `firstZero` gives `count` when the first `count` words hold no zero, and otherwise the index of the first zero. |
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `removeZero_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

`firstZero_cases` is in [the array-search proof](../../Library/Arrays/Search/Proof.lean),
`compute_eq` is in [the proof of the specification](Proof.lean), which the theorems of both
compilers use, and `removeZero_bytes` is in [the proofs](Verify.lean).  They use only `propext`,
`Classical.choice`, and `Quot.sound`.  `compute_eq` connects the loop to `Array.findIdx?` and the
build to `Array.eraseIdx!` through the core lemmas `Array.findIdx?_eq_some_iff_getElem` and
`Array.getElem_eraseIdx`.  The LeanExe theorem allows a trap, and `removeZero_call` of the verified
module excludes it.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.RemoveZero.Verify
mkdir -p build/removeZero
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.RemoveZero.Module Examples.RemoveZero.removeZero.module build/removeZero/removeZero.wasm
build/tools/leanexe-wasmtime-host call build/removeZero/removeZero.wasm compute array-u64 \
  array-u64:7,0,9,0
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[7, 9, 0]`.  [The module
tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run 10 inputs in Wasmtime against
`expected`, including the empty array, arrays of zeros, a zero first and last, and nine words.

## The verified compiler's module

`verified_compile compiled := [firstZero, compute]` in [the verified compilation](Compiled.lean)
generates `compiled.compute.trapFree`, which states that function 3 computes `compute` without a
trap from a store in which `top` can rise by `compiled.compute.bound xs` bytes, and
`compiled.compute.bound_eq`, which gives that bound as one block of the result's length.
`compute_bound` closes the bound to 120 bytes, and `removeZero_call` composes the trap-free theorem
with `compute_eq` through `arrayCall` of [the shared call theorem](../ArrayCall.lean).  The
generated `compiled.firstZero.implements` states that function 2 computes the library's `firstZero`
without a trap, since the loop allocates nothing.

| Theorem | Statement |
|---------|-----------|
| `compute_bound` | The allocation bound of `compute` is at most 120 bytes. |
| `removeZero_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 120 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 120 bytes. |

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

The call prints `[7, 9, 0]`, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) against
`expected`, and `firstZero` on each input with three counts, in Wasmtime with the allocation
counters.  [The native driver](../../tests/native/verified.sh) runs the same cases on the module's
translation to C, compiled with CompCert.

## Related examples

[`Increment`](../Increment/README.md) builds its result in the same way and has a complete-execution
theorem.  [`Updates`](../Updates/README.md) removes an element with `eraseIdxIfInBounds`, in place
when the array is owned.  The LTG entries [`index-loop`](../../ltg/entries/index-loop/README.md) and
[`array-build`](../../ltg/entries/array-build/README.md) describe the rules.

## References

- [The Lean 4 reference on
  arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/), for `Array.findIdx?`
  and `Array.eraseIdx!`.
- [The LeanExe compiler manual's section on
  restrictions](../../docs/leanexe-manual.md#restrictions-and-how-to-write-around-them), on writing
  around constructs the dialect lacks.
