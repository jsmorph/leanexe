# PairSum: a temporary array

## What it is

[The program](Program.lean) returns `a + b` by folding addition over the array literal `#[a, b]`.
The array exists only inside the call: the compiled code allocates it on the module's heap, folds
over it, and releases it before returning.  [The module definition](Module.lean) compiles `pairSum`
into the 1,479-byte `pairSum.wasm`, which exports `pairSum`.

## What it shows

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
`Classical.choice`, and `Quot.sound`.  [The manual](../../docs/manual.md#the-implements-family)
defines `Implements`.  [Its section on proofs](../../docs/manual.md#structure-of-a-proof) describes
the structure of a proof that follows the statements of a body.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.PairSum.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.PairSum.Module Examples.PairSum.pairSum.module build/pairSum/pairSum.wasm
build/tools/leanexe-wasmtime-host call-stats build/pairSum/pairSum.wasm pairSum i64 i64:2 i64:40
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints 42 and `stats 1 1`, the
allocation and free counters.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 34
cases of [`Cases.lean`](Cases.lean) with native Lean, including sums that wrap.

## Related examples

[`SumCount`](../SumCount/README.md) returns its array literal to the caller instead of releasing it.
[`SumArray`](../SumArray/README.md) folds over an array that the caller passes in, with the general
fold rule `Func.foldl_implements`.  The LTG entries
[`array-literal`](../../ltg/entries/array-literal/README.md),
[`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md), and
[`release-temporary`](../../ltg/entries/release-temporary/README.md) describe the three rules.

## References

- [The manual's section on arrays](../../docs/manual.md#arrays), which gives the heap layout of an
  array: a header, a length word, and the elements.
- WebAssembly Core Specification, [memory
  instructions](https://webassembly.github.io/spec/core/syntax/instructions.html#memory-instructions),
  which the allocator and the array code use.
