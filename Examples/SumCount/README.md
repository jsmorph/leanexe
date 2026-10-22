# SumCount: an array result

## `#[sum, size]` from a borrowed array

[The program](Program.lean) takes an array of words and returns the two-element array `#[sum,
size]`, where the sum wraps modulo 2^64.  The input array is borrowed: the caller keeps it, and the
call only reads it.  The result is a new array that the caller owns and must release.  [The module
definition](Module.lean) compiles `sumCount` into the 1,485-byte `sumCount.wasm`.

## Ownership in the postcondition

The body is a fold over the input, a load of its length word, and an array literal of the two
results, and the proof follows those statements with `Func.implements_heap`.  The theorem's
postcondition states that the returned pointer represents the result array, owned by the caller, and
that the input array keeps its bytes.  The host's counters show the two allocations, the input and
the result, and no free.

| Theorem | Statement |
|---------|-----------|
| `sumCount_implements` | Function 2 of `sumCount.module` implements `sumCount`: from any store that satisfies the runtime invariant, with the input array in memory, a call returns an owned array holding `#[sum, size]` or stops at `unreachable`. |
| `sumCount_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `sumCount`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The LeanExe compiler
manual](../../docs/leanexe-manual.md#representations) describes how an argument and a result
represent a Lean value, borrowed or owned.  [The section on
ownership](../../docs/leanexe-manual.md#ownership) gives the rules for who releases an array.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.SumCount.Verify
mkdir -p build/sumCount
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumCount.Module Examples.SumCount.sumCount.module build/sumCount/sumCount.wasm
build/tools/leanexe-wasmtime-host call-stats build/sumCount/sumCount.wasm sumCount array-u64 \
  array-u64:1,2,3
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[6, 3]` and `stats 2 0`.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 35 cases of [`Cases.lean`](Cases.lean)
with native Lean, including the empty array and sums that wrap.

## Related examples

[`PairSum`](../PairSum/README.md) builds an array literal and releases it inside the call.
[`SumArray`](../SumArray/README.md) has the fold alone, with a word result.
[`Updates`](../Updates/README.md) and [`Clob`](../../Demos/Clob/README.md) return arrays that they build by
updating their inputs.  The LTG entries
[`array-literal`](../../ltg/entries/array-literal/README.md),
[`array-size`](../../ltg/entries/array-size/README.md), and
[`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md) describe the rules.

## References

- [The LeanExe compiler manual's section on arrays](../../docs/leanexe-manual.md#arrays), which
  lists the array operations and their compiled forms.
- [The LeanExe compiler manual's section on the Wasmtime
  host](../../docs/leanexe-manual.md#the-wasmtime-host), which describes the `array-u64` argument
  and result kinds and the counters.
