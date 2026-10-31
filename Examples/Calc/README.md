# Calc: an enumeration and a structure

## A calculator over `Op` and `Calc`

[The program](Program.lean) is a calculator over two user-defined types: the enumeration `Op` of
four word operations and the structure `Calc` of a value, a step count, and the last operation.
`calcRun` reads instructions from an array, two words each, and applies them with `Calc.step` in a
`LeanExe.loop` whose state is a `Calc`.  `Calc.undo` matches on the structure's fields to reverse a
last addition or subtraction.  `verified_compile compiled := [Op.apply, …, calcRun]` in [the
verified compilation](Compiled.lean) compiles the functions into the 2,139-byte
`calculator.wasm` of [the module registry](../../tests/verified/modules.txt).

## Structures and enumerations as words

A function of the module takes a structure as the words of its fields and returns one as several
results, so `Calc.step` takes five words and returns three.  An enumeration is the word of its
constructor index, and a match on it compiles to a chain of tests of the word.
[`Flat.lean`](Flat.lean) gives the `Flat` instances that state how the theorems represent the two
types, `Op` as a word and `Calc` as the triple of its fields, and these instances are part of what
the theorems state.

| Theorem | Statement |
|---------|-----------|
| `compiled.apply.implements` … `compiled.calcRun.implements` | Each of functions 2 to 7 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns its Lean function's value without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `calculator_file`, `calculator_file_decode` | `build/verified/calculator.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

No function allocates, so each generated `compiled.f.implements` states that its function returns
the Lean function's value without a trap, and `compiled.f.native` states the same of its C function.
The reflector reads the structure patterns of `Calc.undo`, which fix `last` to `.add` and `.sub` and
bind `value` and `steps`, as two tests of the word of `last` followed by the wildcard's `c`.  The
kernel checks that the tests equal the match by cases on the state and on `last`, as [the verified
compiler manual](../../docs/verified-manual.md#structure-patterns) describes.  The axiom reports of
the file theorems, which depend on every `implements` theorem through `compiled.bytes`, name only
`propext`, `Classical.choice`, and `Quot.sound`.  [The manual's section on records, tuples, and
sums](../../docs/verified-manual.md#records-tuples-and-sums) describes how the reflector reads user
types, and [its section on representations](../../docs/verified-manual.md#representations) describes
the `Flat` class.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Calc.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Calc.Compiled Examples.Calc.compiled.module build/verified/calculator.wasm
build/tools/leanexe-wasmtime-host call build/verified/calculator.wasm calcRun \
  list:i64,i64,i64 array-u64:0,5,2,4,1,6
build/tools/leanexe-wasmtime-host call build/verified/calculator.wasm undo \
  list:i64,i64,i64 i64:14 i64:3 i64:1 i64:6
tests/verified/run.sh --cases calculator
tests/native/verified.sh --module calculator
```

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  The
instructions of the first call add 5, multiply by 4, and subtract 6, and the call prints 14, 3, and
1 on three lines: the value, the step count, and the index of `sub`.  The second call undoes the
last subtraction of 6 and prints 20, 3, and 1.  [The verified driver](../../tests/verified/run.sh)
runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime against native Lean, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  The cases state that no call allocates a block other than the host's instruction array of
`calcRun`, which stays allocated.

## Related examples

[`Shape`](../Shape/README.md) has a sum type, whose constructors carry different fields.
[`Bools`](../Bools/README.md) has `Bool`, the built-in two-constructor enumeration, and a small
structure.  [`Grids`](../Grids/README.md) stores records in arrays, and the Euler and drone programs
use structures such as the solver's `Cell` and the planner's `Choice`.  [The pattern
example](../../Verified/Examples/Patterns.lean) of the verified compiler matches on structure
patterns that fix one field or several, as `Calc.undo` does.

## References

- *The Lean Language Reference*, version 4.34.0-rc2, [Structures and
  Constructors](https://lean-lang.org/doc/reference/4.34.0-rc2/Terms/Structures-and-Constructors/).
