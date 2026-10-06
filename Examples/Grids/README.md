# Grids: arrays of records

## What it is

[The program](Program.lean) has fourteen functions on arrays whose elements are records: `Cell`, a
structure with a nested `Conserved` structure, floats, words, a `Bool`, and a `Phase` enumeration;
`Conserved` alone; a one-field `Mass`; and `Bool`.  They read fields of an element, count elements,
build arrays of records with `LeanExe.build`, update fields with `{ c with … }`, and sum a field in
a loop.  The types mirror the cell states of a fluid solver.  [The module definition](Module.lean)
compiles the fourteen functions into the 3,249-byte `grids.wasm`.

## What it shows

An array of records of `k` components stores each element's components in order, one word each, so
element `i` occupies words `i · k` to `i · k + k − 1`, and the length word holds `n · k`.  A field
read loads one word, guarded by `i < 2^29`, and a read past the end gives the record of zero words,
which equals Lean's default when every field's default is zero.  `cell_default` and its siblings
prove that condition for each type, and `cell_length` and its siblings give the number of
components.

| Theorem | Statement |
|---------|-----------|
| `density_implements` … `totalDensity_implements` | Each of functions 2 to 15 of `grids.module` implements its Lean function, with the arrays in memory in the flat layout. |
| `rampElement_words`, `scaledElement_words` | The words of the element records that `ramp` and `scaled` build, with the float fields as bit patterns. |
| `grids_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all fourteen functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The theorems represent an `Array α` of a flat `α` as
`flatWords xs`, which [the manual](../../docs/manual.md#representations) defines.  The Euler solvers
store their grids in this layout.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Grids.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Grids.Module Examples.Grids.grids.module build/grids/grids.wasm
build/tools/leanexe-wasmtime-host call build/grids/grids.wasm flags array-u64 i64:6
build/tools/leanexe-wasmtime-host call build/grids/grids.wasm totalDensity f64 \
  array-u64:4607182418800017408,0,0,4607182418800017408,4611686018427387904,0,0,4607182418800017408
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  `flags 6` prints `[0, 1, 0, 0, 1, 0]`, the
`Bool` array of `i % 3 == 1`.  The second call passes two `Conserved` records, densities 1.0 and
2.0, as eight words, and prints 4613937818241073152, the bits of 3.0.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 346 cases of
[`Cases.lean`](Cases.lean) with native Lean, including reads past the end.

## Related examples

[`Euler`](../Euler/README.md) stores its grids of cells in this layout and updates them in loops.
[`Calc`](../Calc/README.md) and [`Shape`](../Shape/README.md) have records in locals instead of
arrays.  [`Bools`](../Bools/README.md) has `Bool` values outside arrays.  The LTG entries
[`record-read`](../../ltg/entries/record-read/README.md) and
[`record-build`](../../ltg/entries/record-build/README.md) describe the rules.

## References

- [The manual's section on arrays](../../docs/manual.md#arrays), which gives the compiled form of a
  read of an array of records.
- [The manual's section on `LeanExe.build`](../../docs/manual.md#leanexebuild).
