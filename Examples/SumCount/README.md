# SumCount: an array result

## `#[sum, size]` from a borrowed array

[The program](Program.lean) takes an array of words and returns the two-element array `#[sum,
size]`, where the sum wraps modulo 2^64.  The input array is borrowed: the caller keeps it, and the
call only reads it.  The result is a new array that the caller owns and must release.  The command
`verified_compile compiled := [sumCount]` in [the verified compilation](Compiled.lean) compiles
`sumCount` into the 2,098-byte `sumCount.wasm` of [the module
registry](../../tests/verified/modules.txt).

## Ownership in the postcondition

`compiled.sumCount.implements` states that the returned pointer represents the result array, which
the caller owns, and that every region of the caller's heap keeps its bytes and lies apart from the
result.  [The verified compiler manual's section on
representations](../../docs/verified-manual.md#representations) describes how an argument and a
result represent a Lean value, borrowed or owned.  [Its section on
ownership](../../docs/verified-manual.md#ownership) gives the rules by which the reflector chooses
the mode of an array parameter and the code releases an owned array.

| Theorem | Statement |
|---------|-----------|
| `compiled.sumCount.implements` | Function 2 of `compiled.module`, called with a borrowed array from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns an owned array that holds `#[sum, size]` or stops at `unreachable`. |
| `compiled.sumCount.trapFree` | Function 2, called in the same way, returns the array without a trap when `top` can rise by `compiled.sumCount.bound xs` bytes within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `sumCount`. |
| `sumCount_file`, `sumCount_file_decode` | `build/verified/sumCount.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

The reflector reads the result `#[sum, size]` as two pushes onto `#[]`, so the module allocates an
empty block and grows it at each push.  The generated `compiled.sumCount.bound_eq` charges the
empty block, the first growth, and the paid second push.  When `top` can rise by that bound,
`compiled.sumCount.trapFree` excludes the stop at `unreachable` that `compiled.sumCount.implements`
allows.

## Building, running, and testing

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

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  The call
prints `[6, 3]` and `stats 4 2`: the host's input, the literal's empty block, and the block of each
growth, with the two blocks that the growths replace freed.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean), including the
empty array and sums that wrap, in Wasmtime against native Lean, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  The cases state the two blocks that stay allocated, the input and the result, and at most
four allocations.  Without `--cases`, the verified driver also checks the file module against the
written file and requires the axiom reports of both file theorems to name only `propext`,
`Classical.choice`, and `Quot.sound`.

## Related examples

[`PairSum`](../PairSum/README.md) builds an array literal and releases it inside the call.
[`SumArray`](../SumArray/README.md) has the fold alone, with a word result.
[`Updates`](../Updates/README.md) and [`Clob`](../../Demos/Clob/README.md) return arrays that they
build by updating their inputs.

## References

- [Verified Compiler Manual: Array literals and conditions on
  propositions](../../docs/verified-manual.md#array-literals-and-conditions-on-propositions).
- [Verified Compiler Manual: The Wasmtime host](../../docs/verified-manual.md#the-wasmtime-host).
