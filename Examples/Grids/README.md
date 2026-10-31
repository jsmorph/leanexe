# Grids: arrays of records

## Fourteen functions on arrays of records

[The program](Program.lean) has fourteen functions on arrays whose elements are records: `Cell`, a
structure with a nested `Conserved` structure, floats, words, a `Bool`, and a `Phase` enumeration;
`Conserved` alone; a one-field `Mass`; and `Bool`.  They read fields of an element, count elements,
build arrays of records with `LeanExe.build`, update fields with `{ c with … }`, and sum a field in
a loop.  The types mirror the cell states of a fluid solver.
`verified_compile compiled := [density, …, totalDensity]` in [the verified
compilation](Compiled.lean) compiles the definitions into the 5,237-byte `exampleGrids.wasm` of [the
module registry](../../tests/verified/modules.txt).  The registry names it `exampleGrids`, since
`grids` names [the grid fixture](../../Verified/Examples/Grids.lean) of the verified compiler.

## The flat layout and default records

An array of records of `k` components stores each element's components in order, one word each, so
element `i` occupies words `i · k` to `i · k + k − 1`, and the length word holds `n · k`.  The
theorems represent an `Array α` of a flat `α` as `flatWords xs`, which [the verified compiler
manual](../../docs/verified-manual.md#representations) defines.  The reflector needs the `Flat`
instances of `Phase`, `Conserved`, `Cell`, and `Mass`, which [`Flat.lean`](Flat.lean) states: a
phase as the word of its constructor index, and a state, a cell, and a mass as their fields in
declaration order.  A read past the end returns Lean's default record, and the reflector checks in
the kernel that the flattening of that default is the default of the flattened type, which
requires each field to take its default and an enumeration's default to have the word 0.

The reads, the counts, and `totalDensity` allocate nothing, so their generated `implements`
theorems state a return without a trap.  `scaled`, `ramp`, and `flags` build an array each, and
their `implements` theorems allow a stop at `unreachable`.  Their `trapFree` theorems exclude that
stop when `top` can rise by the bound of the block that the function builds.

| Theorem | Statement |
|---------|-----------|
| `compiled.density.implements` … `compiled.totalDensity.implements` | Functions 2 to 15 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return their Lean functions' values, without a trap for those that allocate nothing. |
| `compiled.scaled.trapFree`, `compiled.ramp.trapFree`, `compiled.flags.trapFree` | `scaled`, `ramp`, and `flags` return their arrays without a trap when `top` can rise by `Verified.blockCost` of the result's words within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `exampleGrids_file`, `exampleGrids_file_decode` | `build/verified/exampleGrids.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

## Building, running, and testing

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

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository README](../../README.md#commands).
`flags 6` prints `[0, 1, 0, 0, 1, 0]`, the `Bool` array of `i % 3 == 1`.  The second call passes
two `Conserved` records, densities 1.0 and 2.0, as eight words, and prints 4613937818241073152, the
bits of 3.0.  [The verified driver](../../tests/verified/run.sh) runs the inputs of
[`Cases.lean`](Cases.lean), reads past the end included, in Wasmtime against native Lean, and [the
native driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled
with CompCert.  The cases state one block left allocated by each function, the host's array or the
result, and two by `scaled`, which reads one array and builds another.

## Related examples

[`Euler`](../../Demos/Euler/README.md) stores its grids of cells in this layout and updates them in
loops.  [`Calc`](../Calc/README.md) and [`Shape`](../Shape/README.md) have records in locals instead
of arrays.  [`Bools`](../Bools/README.md) has `Bool` values outside arrays.  The LTG entries
[`record-read`](../../ltg/entries/record-read/README.md) and
[`record-build`](../../ltg/entries/record-build/README.md) hold proof guidance for reads and builds
of record arrays.

## References

- [Verified Compiler Manual: Types](../../docs/verified-manual.md#types).
- [Verified Compiler Manual: Loops and builds](../../docs/verified-manual.md#loops-and-builds).
