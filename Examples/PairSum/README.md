# PairSum: a temporary array

## `a + b` by a fold over `#[a, b]`

[The program](Program.lean) returns `a + b` by folding addition over the array literal `#[a, b]`.
The array exists only inside the call.  `verified_compile compiled := [pairSum]` in [the verified
compilation](Compiled.lean) compiles the definition into the 2,088-byte `pairSum.wasm` of [the
module registry](../../tests/verified/modules.txt).  The reflector reads
`#[a, b]` as two pushes onto `#[]`, so the module allocates an empty block on its heap, grows it at
each push, folds over it, and releases it before returning.

## Theorems of a call that allocates and frees

The generated `compiled.pairSum.bound_eq` charges the empty block, the first growth, and the paid
second push.  When `top` can rise by that bound, `compiled.pairSum.trapFree` excludes the stop at
`unreachable` that `compiled.pairSum.implements` allows.  Both theorems state `ImplementsA`, which
[the verified compiler manual](../../docs/verified-manual.md#the-implements-family) defines, and its
region clause keeps the bytes of every region of the caller's heap across the call.

| Theorem | Statement |
|---------|-----------|
| `compiled.pairSum.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `a + b` or stops at `unreachable`. |
| `compiled.pairSum.trapFree` | Function 2 returns `a + b` without a trap when `top` can rise by `compiled.pairSum.bound (a, b)` bytes within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `pairSum`. |
| `pairSum_file`, `pairSum_file_decode` | `build/verified/pairSum.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.PairSum.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.PairSum.Compiled Examples.PairSum.compiled.module build/verified/pairSum.wasm
build/tools/leanexe-wasmtime-host call-stats build/verified/pairSum.wasm pairSum i64 i64:2 i64:40
tests/verified/run.sh --cases pairSum
tests/native/verified.sh --module pairSum
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository
README](../../README.md#commands).  The call prints 42 and `stats 3 3`, the allocation and free
counters: the literal's empty block and the block of each growth, all three freed.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean), among them sums
that wrap, in Wasmtime against native Lean, and [the native driver](../../tests/native/verified.sh)
runs them on the module's translation to C, compiled with CompCert.  The cases state that no block
stays allocated and that a call allocates at most three.  Without `--cases`, the verified driver
also checks the file module against the written file and requires the axiom reports of both file
theorems to name only `propext`, `Classical.choice`, and `Quot.sound`.

## Related examples

[`SumCount`](../SumCount/README.md) returns its array literal to the caller instead of releasing it.
[`SumArray`](../SumArray/README.md) folds over an array that the caller passes in.

## References

- [Verified Compiler Manual: Array literals and conditions on
  propositions](../../docs/verified-manual.md#array-literals-and-conditions-on-propositions).
- WebAssembly Core Specification, [Memory
  Instructions](https://webassembly.github.io/spec/core/syntax/instructions.html#memory-instructions).
