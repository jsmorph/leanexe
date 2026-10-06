# Lookup: the first of ten pairs

This example is [main's Demo 2](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-2/README.md), carried to this branch's
pipeline.  [The request](request.txt) asks, for 21 words `[query, key1, value1, …, key10,
value10]`, for `[value, 1]` from the first pair whose key equals the query, and for `[0, 0]` when
no key matches or the input has another length.  [The
specification](../../Project/Lookup/Spec.lean) states it as main's did, with ten ordered
comparisons.

[The program](../../LeanExe/Examples/Lookup.lean) runs a loop over the ten pairs with a found flag
and the value of the first match as its state, and it returns a two-word array literal.  The reads
past the end of a shorter input return 0, which Lean's `xs[i]!` also returns, and the length test
selects `[0, 0]` for such an input.  [The module definition](../../Project/Lookup/Module.lean)
compiles it into a 1,689-byte `lookup.wasm` that exports `compute`.

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `lookup_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

The theorems are in [the proofs](../../Project/Lookup/Verify.lean), and they use only `propext`,
`Classical.choice`, and `Quot.sound`.  Main's proof concerned one 7,336-byte binary and took 1,639
lines.  Here the loop rule and the array-literal rule prove `Implements` for the program, and
with `compute_eq`, proved by ten case splits, `Implements.congr` states it for the specification.  The module tests run main's
sample, a missing key, a match at the first and last pairs, repeated keys, and inputs of 0, 20, and
22 words in Wasmtime against `expected`.

```sh
tools/leanrun --timeout 60m lake build Project.Lookup.Verify
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Lookup.Module Project.Lookup.lookup.module build/lookup/lookup.wasm
build/tools/leanexe-wasmtime-host call build/lookup/lookup.wasm compute array-u64 \
  array-u64:42,1,10,42,20,42,30,4,40,5,50,6,60,7,70,8,80,9,90,10,100
```
