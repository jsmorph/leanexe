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

## The verified compiler's module

`verified_compile compiled := [sumCount]` in [the verified compilation](Compiled.lean) compiles the
same definition into the 2,098-byte `sumCount.wasm` of [the module
registry](../../tests/verified/modules.txt).  The reflector reads the result `#[sum, size]` as two
pushes onto `#[]`, so the module allocates an empty block and grows it at each push, and the
generated `compiled.sumCount.bound_eq` charges the empty block, the first growth, and the paid
second push.  When `top` can rise by that bound, `compiled.sumCount.trapFree` excludes the stop at
`unreachable` that `compiled.sumCount.implements` and `sumCount_bytes` allow.

| Theorem | Statement |
|---------|-----------|
| `compiled.sumCount.implements` | Function 2 of `compiled.module`, called with a borrowed array from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns an owned array that holds `#[sum, size]` or stops at `unreachable`. |
| `compiled.sumCount.trapFree` | The same call returns the array without a trap when `top` can rise by `compiled.sumCount.bound xs` bytes within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `sumCount`. |
| `sumCount_file`, `sumCount_file_decode` | `build/verified/sumCount.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

```sh
tools/leanrun --timeout 60m lake build Examples.SumCount.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumCount.Compiled Examples.SumCount.compiled.module build/verified/sumCount.wasm
build/tools/leanexe-wasmtime-host call-stats build/verified/sumCount.wasm sumCount array-u64 \
  array-u64:1,2,3
tests/verified/run.sh --cases sumCount
tests/native/verified.sh --module sumCount
```

The call prints `[6, 3]` and `stats 4 2`: the host's input, the literal's empty block, and the block
of each growth, with the two blocks that the growths replace freed.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state the two blocks that stay
allocated, the input and the result, and at most four allocations.

## Related examples

[`PairSum`](../PairSum/README.md) builds an array literal and releases it inside the call.
[`SumArray`](../SumArray/README.md) has the fold alone, with a word result.
[`Updates`](../Updates/README.md) and [`Clob`](../../Demos/Clob/README.md) return arrays that they build by
updating their inputs.  The LTG entries
[`array-literal`](../../ltg/entries/array-literal/README.md),
[`array-size`](../../ltg/entries/array-size/README.md), and
[`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md) describe the rules.

## References

- [LeanExe Compiler Manual: Arrays](../../docs/leanexe-manual.md#arrays).
- [LeanExe Compiler Manual: The Wasmtime host](../../docs/leanexe-manual.md#the-wasmtime-host).
