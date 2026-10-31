# Bools: truth values as data

## Functions on `Bool`

[The program](Program.lean) holds small functions that take, return, or store `Bool` values:
tests built with `decide`, `==`, and `!=`, the connectives `&&`, `||`, and `!`, a float equality and
a range test, a selection by `if`, a loop whose state is a `Bool`, and a structure with a `Bool`
field.  A `Bool` is the word of its constructor index, 0 for `false` and 1 for `true`.
`verified_compile compiled := [isPositive, …, flagOf]` in [the verified compilation](Compiled.lean)
compiles them into the 1,892-byte `bools.wasm` of [the module
registry](../../tests/verified/modules.txt).

## Bitwise connectives and per-function theorems

Each function has its own generated theorem, and `compiled.bytes` states them all for the
decoded module.  No function allocates, so each `compiled.f.implements` states that its function
returns the Lean function's value without a trap, and `compiled.f.native` states the same of its C
function.  `&&` and `||` compile to `i64.and` and `i64.or` on the 0-or-1 words, with both operands
evaluated, which gives Lean's result because an operand has no effect, and `!` compiles to
`i64.eqz`, a test for zero.  `floatSame` is IEEE equality, under which NaN equals nothing and the
two zeros are equal, and `anyEqual` carries its `Bool` state through `LeanExe.loop`.  `mark` returns
the structure `Flagged` as two words, its flag and its value.

| Theorem | Statement |
|---------|-----------|
| `compiled.isPositive.implements` … `compiled.flagOf.implements` | Each of functions 2 to 14 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns its Lean function's value without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `bools_file`, `bools_file_decode` | `build/verified/bools.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

The axiom reports of the file theorems, which depend on every `implements` theorem through
`compiled.bytes`, name only `propext`, `Classical.choice`, and `Quot.sound`.  `Bool` has a built-in
`Flat` instance, `cond b 1 0`, which states how a `Bool` argument or result appears to the module,
as [the verified compiler manual](../../docs/verified-manual.md#representations) describes.
`Flagged` takes the representation of [`Flat.lean`](Flat.lean), its flag and its value in
declaration order, and that instance is part of what the theorems state.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Bools.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Bools.Compiled Examples.Bools.compiled.module build/verified/bools.wasm
build/tools/leanexe-wasmtime-host call build/verified/bools.wasm anyEqual i64 i64:10 i64:3
build/tools/leanexe-wasmtime-host call build/verified/bools.wasm mark list:i64,i64 i64:0
tests/verified/run.sh --cases bools
tests/native/verified.sh --module bools
```

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  `anyEqual
10 3` prints 1, since 3 is below 10, and `mark 0` prints 1 and 0 on two lines, the flag and the
value.  [The verified driver](../../tests/verified/run.sh) runs the inputs of
[`Cases.lean`](Cases.lean) in Wasmtime against native Lean, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  The cases state that no call allocates a block.

## Related examples

[`Calc`](../Calc/README.md) and [`Shape`](../Shape/README.md) have user enumerations, structures,
and sums, which the compiler represents the same way.  [`Grids`](../Grids/README.md) stores `Bool`
values in arrays and in record fields.  [`Piecewise`](../Piecewise/README.md) uses the float
comparisons inside conditionals instead of returning them.

## References

- [Verified Compiler Manual: Records, tuples, and
  sums](../../docs/verified-manual.md#records-tuples-and-sums).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Booleans](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Booleans/).
