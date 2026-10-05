# Below 100: a filter of at most eight words

This example is main's Demo 5 (`git show main:demos/demo-5/README.md`), carried to this branch's
pipeline.  [The request](request.txt) asks for the elements of an array of at most eight words
that are less than 100, in their original order, and for the empty array when the input is
longer.  [The specification](../../Project/Below100/Spec.lean) states it with `Array.filter`, as
main's did.

[The program](../../LeanExe/Examples/Below100.lean) repeats `keep` with `LeanExe.repeatWhile`
over the first `count` elements, where `count` is the input's size when it is at most eight and 0
otherwise.  `keep` takes the input, an index, and the output array, which it consumes: it pushes
the element onto the output in place when the element is less than 100.  The dialect has no
`Array.filter`, so the program builds the output with `push`, which moves the output to a larger
block when the block is full.  [The module definition](../../Project/Below100/Module.lean)
compiles `keep` and `compute` into a 1,831-byte `below100.wasm` that exports both.

| Theorem | Statement |
|---------|-----------|
| `keep_go` | `keep` repeated from index `i` with the filtered prefix up to `i` gives the filtered prefix up to `count`. |
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `keep_implements` | Function 2 computes `keep` and consumes the output array, whose block it may replace. |
| `below100_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

The theorems are in [the proofs](../../Project/Below100/Verify.lean), and they use only
`propext`, `Classical.choice`, and `Quot.sound`.  Main's generated proof concerned one 1,975-byte
binary and took 969 lines, reduced to 70 by main's later proof tools.  Here the rules of the
in-place push and of `repeatWhile` over one array prove `Implements`, and `compute_eq` carries it
to the specification.  The module tests run nine inputs in Wasmtime against `expected`, including
the empty array, eight words, and nine words.

```sh
tools/leanrun --timeout 60m lake build Project.Below100.Verify
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Below100.Module Project.Below100.below100.module build/below100/below100.wasm
build/tools/leanexe-wasmtime-host call build/below100/below100.wasm compute array-u64 \
  array-u64:5,100,99,250,0,7
```
