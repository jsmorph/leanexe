# Grids: arrays of records

## Fourteen functions on arrays of records

[The program](Program.lean) has fourteen functions on arrays whose elements are records: `Cell`, a
structure with a nested `Conserved` structure, floats, words, a `Bool`, and a `Phase` enumeration;
`Conserved` alone; a one-field `Mass`; and `Bool`.  They read fields of an element, count elements,
build arrays of records with `LeanExe.build`, update fields with `{ c with … }`, and sum a field in
a loop.  The types mirror the cell states of a fluid solver.  [The module definition](Module.lean)
compiles the fourteen functions into the 3,249-byte `grids.wasm`.

## The flat layout and default records

An array of records of `k` components stores each element's components in order, one word each, so
element `i` occupies words `i · k` to `i · k + k − 1`, and the length word holds `n · k`.  A field
read loads one word, guarded by `i < 2^29`, and a read past the end gives the record of zero words,
which equals Lean's default when every field's default is zero.  `cell_default` and its siblings
prove that condition for each type, and `cell_length` and its siblings give the number of
components.

| Theorem | Statement |
|---------|-----------|
| `density_implements` … `totalDensity_implements` | Each of functions 2 to 15 of `grids.module` implements its Lean function, with the arrays in memory in the flat layout. |
| `rampElement_words`, `scaledElement_words` | Words of the element records that `ramp` and `scaled` build, with the float fields as bit patterns. |
| `grids_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all fourteen functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The theorems represent an `Array α` of a flat `α` as
`flatWords xs`, which [the verified compiler manual](../../docs/verified-manual.md#representations)
defines.  The Euler solvers store their grids in this layout.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Grids.Verify
mkdir -p build/grids
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

## The verified compiler's module

`verified_compile compiled := [density, …, totalDensity]` in [the verified
compilation](Compiled.lean) compiles the definitions, in the order of the LeanExe module, into the
5,237-byte `exampleGrids.wasm` of [the module registry](../../tests/verified/modules.txt).  The
registry names it `exampleGrids`, since `grids` names [the grid
fixture](../../Verified/Examples/Grids.lean) of the verified compiler.  The reflector needs the
`Flat` instances of `Phase`, `Conserved`, `Cell`, and `Mass`, which [`Flat.lean`](Flat.lean) states
for the theorems of both compilers, and the host passes the same words for an array of records to
both modules.  The reads, the counts, and `totalDensity` allocate nothing, so their generated
`implements` theorems state a return without a trap, and `compiled.f.trapFree` excludes the stop at
`unreachable` of `scaled`, `ramp`, and `flags` when `top` can rise by the bound of the one block
that each builds.

| Theorem | Statement |
|---------|-----------|
| `compiled.density.implements` … `compiled.totalDensity.implements` | Functions 2 to 15 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return their Lean functions' values, without a trap for those that allocate nothing. |
| `compiled.scaled.trapFree`, `compiled.ramp.trapFree`, `compiled.flags.trapFree` | The builds return their arrays without a trap when `top` can rise by `Verified.blockCost` of the result's words within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `exampleGrids_file`, `exampleGrids_file_decode` | `build/verified/exampleGrids.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

```sh
tools/leanrun --timeout 60m lake build Examples.Grids.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Grids.Compiled Examples.Grids.compiled.module build/verified/exampleGrids.wasm
build/tools/leanexe-wasmtime-host call build/verified/exampleGrids.wasm flags array-u64 i64:6
build/tools/leanexe-wasmtime-host call build/verified/exampleGrids.wasm totalDensity f64 \
  array-u64:4607182418800017408,0,0,4607182418800017408,4611686018427387904,0,0,4607182418800017408
tests/verified/run.sh --cases exampleGrids
tests/native/verified.sh --module exampleGrids
```

The calls print `[0, 1, 0, 0, 1, 0]` and 4613937818241073152, as the LeanExe module's calls do.
[The verified driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean),
reads past the end included, in Wasmtime against native Lean, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  The cases state one block left allocated by each function, the host's array or the
result, and two by `scaled`, which reads one array and builds another.

## Related examples

[`Euler`](../../Demos/Euler/README.md) stores its grids of cells in this layout and updates them in loops.
[`Calc`](../Calc/README.md) and [`Shape`](../Shape/README.md) have records in locals instead of
arrays.  [`Bools`](../Bools/README.md) has `Bool` values outside arrays.  The LTG entries
[`record-read`](../../ltg/entries/record-read/README.md) and
[`record-build`](../../ltg/entries/record-build/README.md) describe the rules.

## References

- [LeanExe Compiler Manual: Arrays](../../docs/leanexe-manual.md#arrays).
- [LeanExe Compiler Manual: `LeanExe.build`](../../docs/leanexe-manual.md#leanexebuild).
