# Calc: an enumeration and a structure

## What it is

[The program](Program.lean) is a calculator over two user-defined types: the enumeration `Op` of
four word operations and the structure `Calc` of a value, a step count, and the last operation.
`calcRun` reads instructions from an array, two words each, and applies them with `Calc.step` in a
`LeanExe.loop` whose state is a `Calc`.  `Calc.undo` matches on the structure's fields to reverse a
last addition or subtraction.  [The module definition](Module.lean) compiles the six functions into
the 1,913-byte `calculator.wasm`.

## What it shows

The compiler keeps a structure in locals, one per field, passes it as several arguments, and returns
it as several results, so `Calc.step` takes five words and returns three.  An enumeration is the
word of its constructor index, and a match on it is a chain of tests of the index, with the last
alternative unguarded.  [`Flat.lean`](Flat.lean) gives the `Flat` instances that state how the
theorems represent the two types, `Op` as a word and `Calc` as the triple of its fields, and these
instances are part of what the theorems state.

| Theorem | Statement |
|---------|-----------|
| `apply_pure`, `ofWord_pure`, `inverse_pure`, `step_pure`, `undo_pure` | Each of functions 2 to 6 keeps the store and returns its Lean function's value, in the representation of [`Flat.lean`](Flat.lean). |
| `calcRun_implements` | Function 7 implements `calcRun`: with the instruction array in memory, a call returns the final `Calc` or stops at `unreachable`. |
| `calculator_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all six functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The manual](../../docs/manual.md#records-and-user-types)
describes the representation of user types.  Its [section on
representations](../../docs/manual.md#representations) describes the `Flat` class.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Calc.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Calc.Module Examples.Calc.calculator.module build/calculator/calculator.wasm
build/tools/leanexe-wasmtime-host call build/calculator/calculator.wasm calcRun \
  list:i64,i64,i64 array-u64:0,5,2,4,1,6
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The instructions add 5, multiply by 4, and
subtract 6, and the call prints 14, 3, and 1 on three lines: the value, the step count, and the
index of `sub`.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 490 cases of
[`Cases.lean`](Cases.lean) with native Lean over the six exports.

## Related examples

[`Shape`](../Shape/README.md) has a sum type, whose constructors carry different fields.
[`Bools`](../Bools/README.md) has `Bool`, the built-in two-constructor enumeration, and a small
structure.  [`Grids`](../Grids/README.md) stores records in arrays, and the Euler and drone programs
use structures such as the solver's `Cell` and the planner's `Choice`.

## References

- [The Lean 4 reference on structures and
  constructors](https://lean-lang.org/doc/reference/4.34.0-rc2/Terms/Structures-and-Constructors/),
  for the structure instance and update syntax, such as `{ c with value := v }`.
- [The manual's section on records and user types](../../docs/manual.md#records-and-user-types).
