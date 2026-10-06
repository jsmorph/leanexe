# Increment: each element plus one

## What it is

This example is [main's Demo
4](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-4/README.md),
carried to this branch's pipeline.  [The request](request.txt) asks for each element of an array of
at most eight words plus one, with wrapping arithmetic, and for the empty array when the input is
longer.  [The specification](Spec.lean) states that behavior in ordinary Lean, with `Array.map`, as
main's did.

[The program](Program.lean) sets the count to the input's size when it is at most eight and to 0
otherwise, and builds that many words, each the input's word plus one.  One build serves both cases,
because the dialect places builds at the top of a function rather than in a branch.  [The module
definition](Module.lean) compiles it into a 1,524-byte `increment.wasm` that exports `compute`.

## What it shows

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `increment_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |
| `increment_total` | From an allocator whose `top` leaves 120 bytes within the first 16 pages, with 16 pages and a cap that allows them, the call returns the words of `expected` without stopping at `unreachable` and leaves memory at 16 pages. |

The theorems are in [the proofs](Verify.lean), and they use only `propext`, `Classical.choice`, and
`Quot.sound`.  Main's theorem concerned one binary of main's compiler and was proved by stepping
through its instructions, which took 457 lines.  Here the proof of `Implements` applies the rule of
the build template, and with `compute_eq`, `Implements.congr` states it for the specification.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Increment.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Increment.Module Examples.Increment.increment.module build/increment/increment.wasm
build/tools/leanexe-wasmtime-host call build/increment/increment.wasm compute array-u64 \
  array-u64:0,41,18446744073709551615
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[1, 42, 0]`: the last word
wraps.  [The module tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run the
request's samples and edge cases in Wasmtime against `expected`.

## Related examples

[`RemoveZero`](../RemoveZero/README.md) also builds its result with `LeanExe.build`.
[`Euler`](../Euler/README.md) and [`Drone`](../Drone/README.md) have complete-execution theorems
with memory bounds of the same form as `increment_total`.  The LTG entry
[`array-build`](../../ltg/entries/array-build/README.md) describes the build template.

## References

- [The manual's section on total execution and memory
  bounds](../../docs/manual.md#total-execution-and-memory-bounds), which describes `ImplementsA` and
  the budget.
- [The Lean 4 reference on
  arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/), for `Array.map`.
