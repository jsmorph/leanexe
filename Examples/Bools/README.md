# Bools: truth values as data

## What it is

[The program](Program.lean) is thirteen small functions that take, return, or store `Bool` values:
tests built with `decide`, `==`, and `!=`, the connectives `&&`, `||`, and `!`, a float equality and
a range test, a selection by `if`, a loop whose state is a `Bool`, and a structure with a `Bool`
field.  A `Bool` is the word of its constructor index, 0 for `false` and 1 for `true`.  [The module
definition](Module.lean) compiles all thirteen into the 1,798-byte `bools.wasm`.

## What it shows

Each function has its own theorem, and `bools_bytes` states all thirteen for the decoded module.
`&&`, `||`, and `!` compile to bitwise and, or, and exclusive or with 1 on the 0-or-1 words, with
both operands evaluated, which gives Lean's result because an operand has no effect.  `floatSame` is
IEEE equality, under which NaN equals nothing and the two zeros are equal, and `anyEqual` carries
its `Bool` state through `LeanExe.loop`.  `mark` returns the structure `Flagged` as two words, its
flag and its value.

| Theorem | Statement |
|---------|-----------|
| `isPositive_implements` … `flagOf_implements` | Each of functions 2 to 14 of `bools.module` implements its Lean function. |
| `bools_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all thirteen functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The manual's table of word
operations](../../docs/manual.md#words-and-booleans) gives the compiled form of each Boolean
operation.  `Bool` has a built-in `Flat` instance, `cond b 1 0`, which states how a `Bool` argument
or result appears to the module.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Bools.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Bools.Module Examples.Bools.bools.module build/bools/bools.wasm
build/tools/leanexe-wasmtime-host call build/bools/bools.wasm anyEqual i64 i64:10 i64:3
build/tools/leanexe-wasmtime-host call build/bools/bools.wasm mark list:i64,i64 i64:0
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  `anyEqual 10 3` prints 1, since 3 is below 10,
and `mark 0` prints 1 and 0 on two lines, the flag and the value.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 698 cases of
[`Cases.lean`](Cases.lean) with native Lean over the thirteen exports.

## Related examples

[`Calc`](../Calc/README.md) and [`Shape`](../Shape/README.md) have user enumerations, structures,
and sums, which the compiler represents the same way.  [`Grids`](../Grids/README.md) stores `Bool`
values in arrays and in record fields.  [`Piecewise`](../Piecewise/README.md) uses the float
comparisons inside conditionals instead of returning them.

## References

- [The manual's section on records and user types](../../docs/manual.md#records-and-user-types),
  which gives the representation of enumerations and structures.
- [The Lean 4 reference on
  `Bool`](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Booleans/).
