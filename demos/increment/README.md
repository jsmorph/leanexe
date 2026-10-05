# Increment: each element plus one

This example is main's Demo 4 (`git show main:demos/demo-4/README.md`), carried to this branch's
pipeline.  [The request](request.txt) asks for each element of an array of at most eight words
plus one, with wrapping arithmetic, and for the empty array when the input is longer.  [The
specification](../../Project/Increment/Spec.lean) states that behavior in ordinary Lean, with
`Array.map`, exactly as main's did.

[The program](../../LeanExe/Examples/Increment.lean) sets the count to the input's size when it is
at most eight and to 0 otherwise, and builds that many words, each the input's word plus one.  One
build serves both cases, because the dialect places builds at the top of a function rather than
in a branch.  [The module definition](../../Project/Increment/Module.lean) compiles it into a
1,524-byte `increment.wasm` that exports `compute`.

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `increment_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |
| `increment_total` | From an allocator whose `top` leaves 120 bytes within the first 16 pages, with 16 pages and a cap that allows them, the call returns the words of `expected` without stopping at `unreachable` and leaves memory at 16 pages. |

The theorems are in [the proofs](../../Project/Increment/Verify.lean), and they use only
`propext`, `Classical.choice`, and `Quot.sound`.  Main's theorem concerned one binary of main's
compiler and was proved by stepping through its instructions, which took 457 lines; here the
proof of `Implements` applies the rule of the build template, and `compute_eq` carries it to the
specification.  The module tests run the request's samples and edge cases in Wasmtime against
`expected`.

```sh
tools/leanrun --timeout 60m lake build Project.Increment.Verify
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Increment.Module Project.Increment.increment.module build/increment/increment.wasm
build/tools/leanexe-wasmtime-host call build/increment/increment.wasm compute array-u64 \
  array-u64:0,41,18446744073709551615
```
