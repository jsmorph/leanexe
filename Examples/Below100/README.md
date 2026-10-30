# Below 100: a filter of at most eight words

## Request, specification, and program

[The request](request.txt) asks for the elements of an array of at most eight words that are less
than 100, in their original order, and for the empty array when the input is longer.  [The
specification](Spec.lean) states it with `Array.filter`.  [The program](Program.lean) repeats `keep`
with `LeanExe.repeatWhile` over the first `count` elements, where `count` is the input's size when
it is at most eight and 0 otherwise.  `keep` takes the input, an index, and the output array, which
it consumes: it pushes the element onto the output in place when the element is less than 100.  The
dialect has no `Array.filter`, so the program builds the output with `push`, which moves the output
to a larger block when the block is full.  [The module definition](Module.lean) compiles `keep` and
`compute` into a 1,831-byte `below100.wasm` that exports both, and [the verified
compilation](Compiled.lean) compiles the same definitions with the verified compiler into a
2,118-byte module.

## The bytes compute the filter

| Theorem | Statement |
|---------|-----------|
| `keep_go` | `keep` repeated from index `i` with the filtered prefix up to `i` gives the filtered prefix up to `count`. |
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `keep_implements` | Function 2 computes `keep` and consumes the output array, whose block it may replace. |
| `below100_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

`keep_go` and `compute_eq` are in [the proof of the specification](Proof.lean), which the theorems
of both compilers use, and the other theorems are in [the proofs](Verify.lean).  They use only
`propext`, `Classical.choice`, and `Quot.sound`.  The rules of the in-place push and of
`repeatWhile` over one array prove `Implements` for the program.  With `compute_eq`,
`Implements.congr` states it for the specification.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Below100.Verify
mkdir -p build/below100
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Below100.Module Examples.Below100.below100.module build/below100/below100.wasm
build/tools/leanexe-wasmtime-host call build/below100/below100.wasm compute array-u64 \
  array-u64:5,100,99,250,0,7
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[5, 99, 0, 7]`.  [The module
tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run nine inputs in Wasmtime against
`expected`, including the empty array, eight words, and nine words.

## The verified compiler's module

`verified_compile compiled := [keep, compute]` in [the verified compilation](Compiled.lean)
generates `compiled.compute.trapFree`, which states that function 3 computes `compute` without a
trap from a store in which `top` can rise by `compiled.compute.bound xs` bytes.
`compiled.compute.bound_eq` states that bound as the smaller of two loop costs, in which each push
that `keep` makes onto its paid output array costs `paidGrowCost 1`, 80 bytes.  `compute_bound`
closes the bound to 712 bytes: 56 bytes for the empty output array, 16 bytes of its credit, and 80
bytes for each of at most eight pushes.  `below100_call` composes the trap-free theorem with
`compute_eq` through `arrayCall` of [the shared call theorem](../ArrayCall.lean).

| Theorem | Statement |
|---------|-----------|
| `compute_bound` | The allocation bound of `compute` is at most 712 bytes. |
| `below100_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 712 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 712 bytes. |

`below100_bytes` allows a trap at `unreachable`, which `below100_call` excludes under its premise
of room.  The charge of 80 bytes for each push is the amortized cost that [the verified compiler
manual](../../docs/verified-manual.md#bounds-and-total-execution) describes, which pays for the
moves of the output to larger blocks.  The generated `compiled.keep.native` and
`compiled.compute.native` state the computations of the C functions of the module's translation.

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

The call prints `[5, 99, 0, 7]`, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) against
`expected`, and `keep` at four indices with two output arrays, in Wasmtime with the allocation
counters.  [The native driver](../../tests/native/verified.sh) runs the same cases on the module's
translation to C, compiled with CompCert.

## Related examples

[`Updates`](../Updates/README.md) has chains of pushes and other in-place updates.
[`Euler`](../../Demos/Euler/README.md) and [`Drone`](../../Demos/Drone/README.md) use `LeanExe.repeatWhile` for their
main loops.  The LTG entries [`repeat-while`](../../ltg/entries/repeat-while/README.md) and
[`in-place-update`](../../ltg/entries/in-place-update/README.md) describe the rules.

## References

- [LeanExe Compiler Manual: Loops and builds](../../docs/leanexe-manual.md#loops-and-builds).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
