# PairSum: a temporary array

## `a + b` by a fold over `#[a, b]`

[The program](Program.lean) returns `a + b` by folding addition over the array literal `#[a, b]`.
The array exists only inside the call: the compiled code allocates it on the module's heap, folds
over it, and releases it before returning.  [The module definition](Module.lean) compiles `pairSum`
into the 1,479-byte `pairSum.wasm`, which exports `pairSum`.

## Proof of a body that allocates and frees

This is the smallest program that allocates and frees memory.  The IR body is four statements: the
array literal, the accumulator's initial value, the fold, and the release of the array.  The proof
follows those statements with `Func.implements_heap`, the rule for a body that uses the heap, and
the rule lemmas of each statement, `Stmt.arrayLiteral_spec`, `Stmt.fold_spec`, and the release rule.
The theorem's frame clause states that every heap region the caller holds keeps its bytes across the
call.  `Implements` does not state that the temporary is freed, and the host's allocation counters
show that it is: one allocation and one free per call.

| Theorem | Statement |
|---------|-----------|
| `pairSum_implements` | Function 2 of `pairSum.module` implements `pairSum`: from any store that satisfies the runtime invariant, a call returns `a + b` or stops at `unreachable`. |
| `pairSum_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `pairSum`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The LeanExe compiler
manual](../../docs/leanexe-manual.md#the-implements-family) defines `Implements`.  [Its section on
proofs](../../docs/leanexe-manual.md#structure-of-a-proof) describes the structure of a proof that
follows the statements of a body.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.PairSum.Verify
mkdir -p build/pairSum
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.PairSum.Module Examples.PairSum.pairSum.module build/pairSum/pairSum.wasm
build/tools/leanexe-wasmtime-host call-stats build/pairSum/pairSum.wasm pairSum i64 i64:2 i64:40
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints 42 and `stats 1 1`, the
allocation and free counters.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 34
cases of [`Cases.lean`](Cases.lean) with native Lean, including sums that wrap.

## The verified compiler's module

`verified_compile compiled := [pairSum]` in [the verified compilation](Compiled.lean) compiles the
same definition into the 2,088-byte `pairSum.wasm` of [the module
registry](../../tests/verified/modules.txt).  The reflector reads `#[a, b]` as two pushes onto
`#[]`, so the module allocates an empty block and grows it at each push, and it releases the array
after the fold.  The generated `compiled.pairSum.bound_eq` charges the empty block, the first
growth, and the paid second push.  When `top` can rise by that bound, `compiled.pairSum.trapFree`
excludes the stop at `unreachable` that `compiled.pairSum.implements` and `pairSum_bytes` allow.

| Theorem | Statement |
|---------|-----------|
| `compiled.pairSum.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `a + b` or stops at `unreachable`. |
| `compiled.pairSum.trapFree` | The same call returns `a + b` without a trap when `top` can rise by `compiled.pairSum.bound (a, b)` bytes within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `pairSum`. |
| `pairSum_file`, `pairSum_file_decode` | `build/verified/pairSum.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

```sh
tools/leanrun --timeout 60m lake build Examples.PairSum.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.PairSum.Compiled Examples.PairSum.compiled.module build/verified/pairSum.wasm
build/tools/leanexe-wasmtime-host call-stats build/verified/pairSum.wasm pairSum i64 i64:2 i64:40
tests/verified/run.sh --cases pairSum
tests/native/verified.sh --module pairSum
```

The call prints 42 and `stats 3 3`: the literal's empty block and the block of each growth, all
three freed, where the LeanExe module allocates the literal once and frees it.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state that no block stays allocated
and that a call allocates at most three.

## Related examples

[`SumCount`](../SumCount/README.md) returns its array literal to the caller instead of releasing it.
[`SumArray`](../SumArray/README.md) folds over an array that the caller passes in, with the general
fold rule `Func.foldl_implements`.  The LTG entries
[`array-literal`](../../ltg/entries/array-literal/README.md),
[`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md), and
[`release-temporary`](../../ltg/entries/release-temporary/README.md) describe the three rules.

## References

- [LeanExe Compiler Manual: Arrays](../../docs/leanexe-manual.md#arrays).
- WebAssembly Core Specification, [Memory
  Instructions](https://webassembly.github.io/spec/core/syntax/instructions.html#memory-instructions).
