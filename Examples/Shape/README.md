# Shape: a sum type

## What it is

[The program](Program.lean) declares `Shape`, a sum of three constructors with different fields: a
circle of float radius, a rectangle of word sides, and a point.  Its functions compute an area with
3 in place of π, build a shape from three words, scale it, read a rectangle's width, grow a
rectangle, and normalize a point into an empty rectangle.  `totalArea` sums the areas of the shapes
that an array encodes, three words each, in a loop with a float state.  [The module
definition](Module.lean) compiles the seven functions into the 2,232-byte `shapes.wasm`.

## What it shows

The compiler represents a sum as a tuple: the constructor index, then one slot for each field of
each constructor, with zeros in the slots of the other constructors.  For `Shape` that is a word, a
float, and two words, as the `Flat` instance in [`Flat.lean`](Flat.lean) states.  A match on a sum
tests the index and reads the fields of the matching constructor.  `Shape.normalize` matches on the
result of `Shape.ofWords`, so a sum flows from one function's result into another's case split.

| Theorem | Statement |
|---------|-----------|
| `area_pure`, `ofWords_pure`, `scale_pure`, `width_pure`, `grow_pure`, `normalize_pure` | Each of functions 2 to 7 keeps the store and returns its Lean function's value, in the representation of [`Flat.lean`](Flat.lean). |
| `totalArea_implements` | Function 8 implements `totalArea`: with the array in memory, a call returns the bits of the total area or stops at `unreachable`. |
| `shapes_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all seven functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  Float literals in the proofs, such as the bits of 3.0, are
closed by `decide +kernel`, and the float operations by the binary64 lemmas of
[`Axpy`](../Axpy/README.md).  [The manual](../../docs/manual.md#records-and-user-types) describes
the representation of user types.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Shape.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Shape.Module Examples.Shape.shapes.module build/shapes/shapes.wasm
build/tools/leanexe-wasmtime-host call build/shapes/shapes.wasm totalArea f64 \
  array-u64:0,2,0,1,3,4,2,0,0
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The array encodes a circle of radius 2, a 3 by 4
rectangle, and a point, and the call prints 4627448617123184640, the bits of 24.0.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 226 cases of
[`Cases.lean`](Cases.lean) with native Lean over the seven exports.

## Related examples

[`Calc`](../Calc/README.md) has an enumeration and a structure, the two simpler kinds of user type.
[`Grids`](../Grids/README.md) stores an enumeration and structures in arrays.
[`Words`](../Words/README.md) and [`Trees`](../Trees/README.md) have recursive types, which the
compiler stores on the heap as records instead of in locals.

## References

- [The Lean 4 reference on inductive
  types](https://lean-lang.org/doc/reference/4.34.0-rc2/The-Type-System/Inductive-Types/).
- [The manual's section on conditionals and case
  splits](../../docs/manual.md#conditionals-and-case-splits), which gives the compiled form of a
  match.
