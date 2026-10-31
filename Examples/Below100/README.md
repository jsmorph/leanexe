# Below 100: a filter of at most eight words

## Request, specification, and program

[The request](request.txt) asks for the elements of an array of at most eight words that are less
than 100, in their original order, and for the empty array when the input is longer.  [The
specification](Spec.lean) states it with `Array.filter`.  [The program](Program.lean) repeats `keep`
with `LeanExe.repeatWhile` over the first `count` elements, where `count` is the input's size when
it is at most eight and 0 otherwise.  `keep` takes the input, an index, and the output array, which
it consumes: it pushes the element onto the output in place when the element is less than 100.  The
verified compiler does not read `Array.filter`, so the program builds the output with `push`, which moves the output
to a larger block when the block is full.  `verified_compile compiled := [keep, compute]` in [the
verified compilation](Compiled.lean) compiles both definitions into a 2,118-byte module.

## The bytes compute the filter

`verified_compile` generates `compiled.compute.trapFree`, which states that function 3 computes
`compute` without a trap from a store in which `top` can rise by `compiled.compute.bound xs` bytes.
`compiled.compute.bound_eq` states that bound as the smaller of two loop costs, in which each push
that `keep` makes onto its paid output array costs `paidGrowCost 1`, 80 bytes.  `compute_bound`
closes the bound to 712 bytes: 56 bytes for the empty output array, 16 bytes of its credit, and 80
bytes for each of at most eight pushes.  `below100_call` composes the trap-free theorem with
`compute_eq` through `arrayCall` of [the shared call theorem](../ArrayCall.lean).

| Theorem | Statement |
|---------|-----------|
| `keep_go` | `keep` repeated from index `i` with the filtered prefix up to `i` gives the filtered prefix up to `count`. |
| `compute_eq` | Program equals the specification on every array of fewer than 2^64 words. |
| `compute_bound` | Allocation bound of `compute` is at most 712 bytes. |
| `below100_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 712 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 712 bytes. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `keep` and `compute`. |
| `below100_file`, `below100_file_decode` | `build/verified/below100.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

`keep_go` and `compute_eq` are in [the proof of the specification](Proof.lean), and
`compute_bound` and `below100_call` are in the verified compilation.  The theorems use only
`propext`, `Classical.choice`, and `Quot.sound`.  The charge of 80 bytes for each push is the
amortized cost that [the verified compiler
manual](../../docs/verified-manual.md#bounds-and-total-execution) describes, which pays for the
moves of the output to larger blocks.  The generated `compiled.keep.native` and
`compiled.compute.native` state the computations of the C functions of the module's translation.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Below100.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Below100.Compiled Examples.Below100.compiled.module build/verified/below100.wasm
build/tools/leanexe-wasmtime-host call build/verified/below100.wasm compute array-u64 \
  array-u64:5,100,99,250,0,7
tests/verified/run.sh --cases below100
tests/native/verified.sh --module below100
```

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  The call
prints `[5, 99, 0, 7]`.  [The verified driver](../../tests/verified/run.sh) compares `compute` with
`expected` on the inputs of [`Cases.lean`](Cases.lean), which include the empty array, eight words,
and nine words, and runs `keep` at four indices with two output arrays on each input, in Wasmtime
with the allocation counters.  [The native driver](../../tests/native/verified.sh) runs the same
cases on the module's translation to C, compiled with CompCert.

## Related examples

[`Updates`](../Updates/README.md) has chains of pushes and other in-place updates.
[`Euler`](../../Demos/Euler/README.md) and [`Drone`](../../Demos/Drone/README.md) use
`LeanExe.repeatWhile` for their main loops.  The VKB entry
[`loop-combinators`](../../VKB/entries/loop-combinators/README.md) describes the induction on the
fuel of `LeanExe.repeatWhile` that `keep_go` uses.

## References

- [Verified Compiler Manual: Loops and builds](../../docs/verified-manual.md#loops-and-builds).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
