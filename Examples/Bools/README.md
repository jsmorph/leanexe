# Bools: truth values as data

## Thirteen functions on `Bool`

[The program](Program.lean) is thirteen small functions that take, return, or store `Bool` values:
tests built with `decide`, `==`, and `!=`, the connectives `&&`, `||`, and `!`, a float equality and
a range test, a selection by `if`, a loop whose state is a `Bool`, and a structure with a `Bool`
field.  A `Bool` is the word of its constructor index, 0 for `false` and 1 for `true`.  [The module
definition](Module.lean) compiles all thirteen into the 1,798-byte `bools.wasm`.

## Bitwise connectives and per-function theorems

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
`Classical.choice`, and `Quot.sound`.  [The LeanExe compiler manual's table of word
operations](../../docs/leanexe-manual.md#words-and-booleans) gives the compiled form of each Boolean
operation.  `Bool` has a built-in `Flat` instance, `cond b 1 0`, which states how a `Bool` argument
or result appears to the module.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Bools.Verify
mkdir -p build/bools
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

## The verified compiler's module

`verified_compile compiled := [isPositive, …, flagOf]` in [the verified
compilation](Compiled.lean) compiles the thirteen definitions, in the order of the LeanExe module,
into the 1,892-byte `bools.wasm` of [the module registry](../../tests/verified/modules.txt), so that
each function has the same index in both modules.  `Flagged` takes the representation of
[`Flat.lean`](Flat.lean), which the theorems of both compilers import.  No function allocates, so
each generated `compiled.f.implements` states that its function returns the Lean function's value
without a trap, and `compiled.f.native` states the same of its C function.

| Theorem | Statement |
|---------|-----------|
| `compiled.isPositive.implements` … `compiled.flagOf.implements` | Each of functions 2 to 14 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns its Lean function's value without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements all thirteen functions. |
| `bools_file`, `bools_file_decode` | `build/verified/bools.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

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

The calls print 1, and 1 and 0, as the LeanExe module's calls do.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state that no call allocates a block.

## Related examples

[`Calc`](../Calc/README.md) and [`Shape`](../Shape/README.md) have user enumerations, structures,
and sums, which the compiler represents the same way.  [`Grids`](../Grids/README.md) stores `Bool`
values in arrays and in record fields.  [`Piecewise`](../Piecewise/README.md) uses the float
comparisons inside conditionals instead of returning them.

## References

- [LeanExe Compiler Manual: Records and user
  types](../../docs/leanexe-manual.md#records-and-user-types).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Booleans](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Booleans/).
