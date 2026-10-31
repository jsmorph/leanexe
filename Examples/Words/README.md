# Words: a list type declared by the program

## Three functions on `Words`

[The program](Program.lean) declares `Words`, a list of words with the constructors `nil` and
`cons`, and three functions on it.  `Words.first` returns the first word or 0, `Words.sumAcc` adds
the words to an accumulator by tail recursion, and `Words.range n` builds the words below `n` with a
loop.  The verified compiler compiles them in [the recursive-type
example](../../Verified/Examples/RecursiveTypes.lean).

## Record layout and tail recursion over records

A user recursive type with one constructor without fields and one with fields gets the record layout
of `List UInt64`: `nil` is the null pointer, and `cons x w` is a record of two slots, the word `x`
and the pointer to `w`.  The program states that layout through the `Encode` instance in
[`Encode.lean`](Encode.lean), with hand-written proofs for the instances `EncodeSlotted` and
`EncodeWellFormed`.  [The
derivation](Reflected.lean) runs `verified_recursive_type` for `Words` in a module apart from the
encoding, so that the verified compiler's programs over the type share one set of conversions and
lemmas.  `sumAcc` is tail recursion over records, which the verified compiler compiles as a loop, so
a call returns on lists longer than the depth limit of guarded recursion.  [The verified compiler
manual's section on ownership](../../docs/verified-manual.md#ownership) gives the rules for
user-defined recursive types, and [its section on
representations](../../docs/verified-manual.md#representations) describes `Encode`,
`EncodeWellFormed`, and `EncodeSlotted`.

## The verified compiler's module

[The recursive-type example](../../Verified/Examples/RecursiveTypes.lean), `recursivetypes` in [the
module registry](../../tests/verified/modules.txt), imports [the derivation](Reflected.lean) and
compiles `Words.first`, `Words.range`, and `Words.sumAcc` beside definitions of its own over
`Words`: the identity, a duplication into a pair, the empty list, a word put in front of a list, and
`reverseWords`, which reverses a list onto an accumulator by tail recursion.  The same module
compiles functions over the `KeyTree` of [`Trees`](../Trees/README.md).  Its cases convert lists
with `Words.ofList` and `Words.toList` of [`Cases.lean`](Cases.lean), and their allocation counts
show that `first` and `sumAcc` allocate nothing, that `range n` allocates `n` records, and that
`reverseWords` builds its result from the records of its arguments without allocating.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, for `f` among `first`, `range`, and `sumAcc` | Each function of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, with each list in the representation of [`Encode.lean`](Encode.lean), returns its Lean function's result, owned by the caller, or stops at `unreachable` when its `aborts` flag allows it. |
| `compiled.f.trapFree` | Calls of these functions return without a trap when `top` can rise by the function's allocation bound within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `recursivetypes_file`, `recursivetypes_file_decode` | `build/verified/recursivetypes.wasm` holds the module's encoding and decodes to the module, as [the file module](../../Verified/Examples/RecursiveTypesFile.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.RecursiveTypes
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.RecursiveTypes \
  Verified.Examples.RecursiveTypes.compiled.module build/verified/recursivetypes.wasm
build/tools/leanexe-wasmtime-host call build/verified/recursivetypes.wasm range chain-u64 i64:4
build/tools/leanexe-wasmtime-host call build/verified/recursivetypes.wasm sumAcc i64 i64:10 \
  chain-u64:1,2,3
tests/verified/run.sh --cases recursivetypes
tests/native/verified.sh --module recursivetypes
```

The commands build the module and its theorems, write the module, call it in the Wasmtime host, and
run the drivers, with the setup of [the repository README](../../README.md#commands).  The first
call prints `[0, 1, 2, 3]`, and the second prints 16, the accumulator 10 plus 1, 2, and 3.  [The
verified driver](../../tests/verified/run.sh) compares the cases of [the recursive-type
cases](../../Verified/Examples/RecursiveTypesCases.lean), among them a list of 4,096 words and
`range` at 1,000 and 4,096, between the Wasmtime host and native Lean, and it checks the blocks left
allocated and the number of allocations.  [The native driver](../../tests/native/verified.sh) runs
the same cases on the module's translation to C, compiled with CompCert, for the exports that the
translation contains.  The full run of the verified driver also checks the file module against the
written file and requires both file theorems to report only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## Related examples

[`Lists`](../Lists/README.md) has the same layout for Lean's `List UInt64`, with a fold instead of
tail recursion.  [`Trees`](../Trees/README.md) has a recursive type with two children and non-tail
recursion.  [`Gcd`](../../Library/Numerics/Arithmetic/Gcd/README.md) has tail recursion on words.
The LTG entries [`tail-recursion-records`](../../ltg/entries/tail-recursion-records/README.md),
[`node-match`](../../ltg/entries/node-match/README.md), and
[`list-cell`](../../ltg/entries/list-cell/README.md) describe tail recursion over records, matches
on recursive values, and list cells.

## References

- *The Lean Language Reference*, version 4.34.0-rc2, [Inductive
  Types](https://lean-lang.org/doc/reference/4.34.0-rc2/The-Type-System/Inductive-Types/).
- [Verified Compiler Manual: Calls and
  recursion](../../docs/verified-manual.md#calls-and-recursion).
