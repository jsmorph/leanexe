# Shape: a sum type

## `Shape`, a sum of three constructors

[The program](Program.lean) declares `Shape`, a sum of three constructors with different fields: a
circle of float radius, a rectangle of word sides, and a point.  Its functions compute an area with
3 in place of π, build a shape from three words, scale it, read a rectangle's width, grow a
rectangle, and normalize a point into an empty rectangle.  `totalArea` sums the areas of the shapes
that an array encodes, three words each, in a loop with a float state.  The verified compiler
compiles them in [the sum example](../../Verified/Examples/Sums.lean).

## Sums as tuples

The verified compiler reads `Shape` through the `Flat` instance of [`Flat.lean`](Flat.lean), which
maps a shape to a word, a float, and two words: the constructor index, the circle's radius, and the
rectangle's sides, with zeros in the fields of the other constructors.  A match on a sum tests the
index and takes the fields of the matching constructor from their positions in the tuple, and the
kernel checks this translation by cases on the constructors.  `Shape.normalize` matches on the
result of `Shape.ofWords`, so a sum flows from one function's result into another's case split, and
the wildcards of `Shape.grow` and `Shape.normalize` bind the matched value.  [The verified compiler
manual's section on sums](../../docs/verified-manual.md#records-tuples-and-sums) gives the rules for
a sum's `Flat` instance and its matches.

## The sum example

`verified_compile compiled` in [the sum example](../../Verified/Examples/Sums.lean) lists the
program's functions first, from `Shape.area` to `totalArea`, so they are functions 2 to 8 of
`compiled.module`, and [the module registry](../../tests/verified/modules.txt) names the module
`sums`.  The functions after them read, set, push, and fold over arrays of shapes, grow a shape in a
loop whose state is the shape, and compute with `Packet`, a sum with a binary32 field and a field of
the enumeration `Mode`.  The `Flat` instance is part of what the theorems state, since they give
each shape as the words of its tuple.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, for `f` from `area` to `totalArea` | Functions 2 to 8 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return the words of their Lean functions' results, or stop at `unreachable` when the function's `aborts` flag allows it. |
| `compiled.f.trapFree` | Calls of these functions return without a trap when `top` can rise by the function's allocation bound within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `sums_file`, `sums_file_decode` | `build/verified/sums.wasm` holds the module's encoding and decodes to the module, as [the file module](../../Verified/Examples/SumsFile.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.Sums
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Verified.Examples.Sums Verified.Examples.Sums.compiled.module build/verified/sums.wasm
build/tools/leanexe-wasmtime-host call build/verified/sums.wasm totalArea f64 \
  array-u64:0,2,0,1,3,4,2,0,0
tests/verified/run.sh --cases sums
tests/native/verified.sh --module sums
```

The commands build the module and its theorems, write the module, call it in the Wasmtime host, and
run the drivers, with the setup of [the repository README](../../README.md#commands).  The array
encodes a circle of radius 2, a 3-by-4 rectangle, and a point, and the call prints
4627448617123184640, the bits of 24.0.  [The verified driver](../../tests/verified/run.sh) runs
`tests/modules/run.sh --module shapes build/verified/sums.wasm`, which computes the 226 cases of
[`Cases.lean`](Cases.lean), written for the module name `shapes`, with native Lean and compares each
with the Wasmtime host's result.

The verified driver then compares the cases of `sums` in [the verified compiler's
cases](../../Verified/Examples/Cases.lean), which cover the array, loop, and `Packet` functions
with shapes written by `shapeArgs` and `shapeWords` of `Cases.lean`, and it checks the blocks left
allocated and the number of allocations.  Its full run also checks the file module against the
written file and requires both file theorems to report only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The native driver](../../tests/native/verified.sh) runs both
sets of cases on the module's translation to C, compiled with CompCert, for the exports that the
translation contains, and it takes the cases of `Cases.lean` from [the native case
generator](../../tests/TestSupport/Native/ModuleCases.lean).

## Related examples

[`Calc`](../Calc/README.md) has an enumeration and a structure, the two simpler kinds of user type.
[`Grids`](../Grids/README.md) stores an enumeration and structures in arrays.
[`Words`](../Words/README.md) and [`Trees`](../Trees/README.md) have recursive types, which the
verified compiler stores on the heap as records instead of in locals.

## References

- *The Lean Language Reference*, version 4.34.0-rc2, [Inductive
  Types](https://lean-lang.org/doc/reference/4.34.0-rc2/The-Type-System/Inductive-Types/).
- [Verified Compiler Manual: Types](../../docs/verified-manual.md#types).
