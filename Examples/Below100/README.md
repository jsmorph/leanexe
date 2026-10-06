# Below 100: a filter of at most eight words

## What it is

This example takes a request in English to a specification, a program, and a theorem that the
module's bytes compute the specification.  [The request](request.txt) asks for the elements of
an array of at most eight words that are less than 100, in their original order, and for the empty
array when the input is longer.  [The specification](Spec.lean) states it with `Array.filter`.

[The program](Program.lean) repeats `keep` with `LeanExe.repeatWhile` over the first `count`
elements, where `count` is the input's size when it is at most eight and 0 otherwise.  `keep` takes
the input, an index, and the output array, which it consumes: it pushes the element onto the output
in place when the element is less than 100.  The dialect has no `Array.filter`, so the program
builds the output with `push`, which moves the output to a larger block when the block is full.
[The module definition](Module.lean) compiles `keep` and `compute` into a 1,831-byte `below100.wasm`
that exports both.

## What it shows

| Theorem | Statement |
|---------|-----------|
| `keep_go` | `keep` repeated from index `i` with the filtered prefix up to `i` gives the filtered prefix up to `count`. |
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `keep_implements` | Function 2 computes `keep` and consumes the output array, whose block it may replace. |
| `below100_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), and they use only `propext`, `Classical.choice`, and
`Quot.sound`.  The rules of the in-place push and of `repeatWhile` over one array prove
`Implements` for the program.  With `compute_eq`, `Implements.congr` states it for the
specification.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Below100.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Below100.Module Examples.Below100.below100.module build/below100/below100.wasm
build/tools/leanexe-wasmtime-host call build/below100/below100.wasm compute array-u64 \
  array-u64:5,100,99,250,0,7
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[5, 99, 0, 7]`.  [The module
tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run nine inputs in Wasmtime against
`expected`, including the empty array, eight words, and nine words.

## Related examples

[`Updates`](../Updates/README.md) has chains of pushes and other in-place updates.
[`Euler`](../Euler/README.md) and [`Drone`](../Drone/README.md) use `LeanExe.repeatWhile` for their
main loops.  The LTG entries [`repeat-while`](../../ltg/entries/repeat-while/README.md) and
[`in-place-update`](../../ltg/entries/in-place-update/README.md) describe the rules.

## References

- [The manual's section on loops and builds](../../docs/manual.md#loops-and-builds), which describes
  `LeanExe.repeatWhile`.
- [The Lean 4 reference on
  arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/), for `Array.filter`
  and `Array.push`.
