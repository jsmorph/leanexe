# Calc: an enumeration and a structure

## A calculator over `Op` and `Calc`

[The program](Program.lean) is a calculator over two user-defined types: the enumeration `Op` of
four word operations and the structure `Calc` of a value, a step count, and the last operation.
`calcRun` reads instructions from an array, two words each, and applies them with `Calc.step` in a
`LeanExe.loop` whose state is a `Calc`.  `Calc.undo` matches on the structure's fields to reverse a
last addition or subtraction.  [The module definition](Module.lean) compiles the six functions into
the 1,913-byte `calculator.wasm`.

## Structures in locals and enumerations as words

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
`Classical.choice`, and `Quot.sound`.  [The LeanExe compiler
manual](../../docs/leanexe-manual.md#records-and-user-types) describes the representation of user
types.  [The verified compiler manual's section on
representations](../../docs/verified-manual.md#representations) describes the `Flat` class.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Calc.Verify
mkdir -p build/calculator
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

## The verified compiler's module

`verified_compile compiled := [Op.apply, …, calcRun]` in [the verified
compilation](Compiled.lean) compiles the unchanged definitions, in the order of the LeanExe module,
into the 2,139-byte `calculator.wasm` of [the module registry](../../tests/verified/modules.txt), so
that each function has the same index in both modules.  `Op` and `Calc` take the representations
of [`Flat.lean`](Flat.lean), which the theorems of both compilers import.  The reflector reads the
structure patterns of `Calc.undo`, which fix `last` to `.add` and `.sub` and bind `value` and
`steps`, as two tests of the word of `last` followed by the wildcard's `c`.  The kernel checks that
the tests equal the match by cases on the state and on `last`, as [the verified compiler
manual](../../docs/verified-manual.md#structure-patterns) describes.  No function allocates, so
each generated `compiled.f.implements` states that its function returns the Lean function's value
without a trap, and `compiled.f.native` states the same of its C function.

| Theorem | Statement |
|---------|-----------|
| `compiled.apply.implements` … `compiled.calcRun.implements` | Each of functions 2 to 7 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns its Lean function's value without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `calculator_file`, `calculator_file_decode` | `build/verified/calculator.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

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

The first call prints 14, 3, and 1, as the LeanExe module's call does, and the second undoes
the last subtraction of 6 and prints 20, 3, and 1.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state that no call allocates a block
other than the host's instruction array of `calcRun`, which stays allocated.

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
