# Words: a list type declared by the program

## What it is

[The program](Program.lean) declares `Words`, a list of words with the constructors `nil` and
`cons`, and three functions on it.  `Words.first` returns the first word or 0, `Words.sumAcc` adds
the words to an accumulator by tail recursion, and `Words.range n` builds the words below `n` with a
loop.  [The module definition](Module.lean) compiles the three into the 1,648-byte `words.wasm`.

## What it shows

A user recursive type with one constructor without fields and one with fields gets the record layout
of `List UInt64`: `nil` is the null pointer, and `cons x w` is a record of two slots.  The program
states that layout through the `Encode` and `EncodeSlotted` instances in
[`Encode.lean`](Encode.lean), which the theorems use.  `sumAcc` is tail recursion over records: the
compiler turns it into a loop that reads the record's slots and follows the pointer, and
`sumAcc_step` proves one iteration.

| Theorem | Statement |
|---------|-----------|
| `first_implements` | Function 2 of `words.module` implements `Words.first`. |
| `sumAcc_step` | One iteration of the compiled loop of `sumAcc`: on `nil` it stores the accumulator, and on `cons x r` it moves to `(acc + x, r)`, which has the same sum and a smaller list. |
| `sumAcc_implements` | Function 3 implements `Words.sumAcc`. |
| `range_implements` | Function 4 implements `Words.range`: a call returns a chain of records, owned by the caller, or stops at `unreachable`. |
| `words_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all three functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The manual](../../docs/manual.md#records-and-user-types)
gives the rules for recursive types.  Its [section on
representations](../../docs/manual.md#representations) describes `Encode` and `EncodeSlotted`.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Words.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Words.Module Examples.Words.words.module build/words/words.wasm
build/tools/leanexe-wasmtime-host call build/words/words.wasm range chain-u64 i64:4
build/tools/leanexe-wasmtime-host call build/words/words.wasm sumAcc i64 i64:10 chain-u64:1,2,3
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The first call prints `[0, 1, 2, 3]`, and the
second prints 16, the accumulator 10 plus 1, 2, and 3.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 26 cases of [`Cases.lean`](Cases.lean)
with native Lean.

## Related examples

[`Lists`](../Lists/README.md) has the same layout for Lean's `List UInt64`, with a fold instead of
tail recursion.  [`Trees`](../Trees/README.md) has a recursive type with two children and non-tail
recursion.  [`Gcd`](../Gcd/README.md) has tail recursion on words.  The LTG entries
[`tail-recursion-records`](../../ltg/entries/tail-recursion-records/README.md),
[`node-match`](../../ltg/entries/node-match/README.md), and
[`list-cell`](../../ltg/entries/list-cell/README.md) describe the rules.

## References

- [The Lean 4 reference on inductive
  types](https://lean-lang.org/doc/reference/4.34.0-rc2/The-Type-System/Inductive-Types/).
- [The manual's section on recursion](../../docs/manual.md#recursion).
