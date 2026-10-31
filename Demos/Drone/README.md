# Drone: terrain-following flight plans

## The planning problem

The drone planner computes a flight over up to 64 stations of terrain, 100 units apart, with heights
from 0 to 1,000,000.  At each station the drone is in one of 45 states, 9 altitudes 25 apart above
the station's floor and 5 horizontal speeds from 0 to 20, and the planner finds the admitted flight
of least duration, with the altitude above the floors as the second criterion.  The output is the
altitude and speed at each station, from rest on the ground at the first station to rest on the
ground at the last.  The theorems state that the bytes of the verified compiler's module compute
the planner, that the planner's flights are optimal and safe, and that a call from a ready store
under a memory cap of at least 35 pages returns without a trap.

## Implementation and theorems

[The planner](Program.lean) uses `UInt64` words and counted loops throughout.  Its square root and
the proof of the square root come from [the arithmetic library's bounded ceiling square
root](../../Library/Numerics/Arithmetic/CeilSqrt/README.md), which takes 17 halvings.  A row is a
build over the 45 targets of loops over the 45 sources, the forward pass carries one table of all
rows, and the output follows the parents back from the last station.  [The
compilation](Verified.lean) compiles the planner unchanged with `verified_compile` and lists
`floorAt` and `best` as functions.  The reflector reads the constants `stateCount`, `infinity`, and
`unreachable` as their values, and [the representation of `Choice`](Flat.lean) gives each choice as
its three words.  The other Lean files of this directory hold the mathematics of the flights and
[the table that `extend` builds](Extend.lean), with its size.

| Claim | Statement | Theorem |
|-------|-----------|---------|
| Optimality | Decoded from the module's bytes, `compiled.module` has a `compute` export, entry 18, that returns the words of the Lean function `compute` or traps at `unreachable`.  For terrain within the bounds, those words have two per station and encode an admitted flight, and no admitted flight from rest at the first station to rest at the last has a smaller (duration, excess) cost.  Empty or invalid terrain gives `#[]`. | `drone_compute` in [the compilation](Verified.lean), from `compute_correct` in [the output proofs](Correct.lean) |
| Flight safety | For terrain within the bounds, the point-mass trajectory that the words define departs and arrives on the ground at rest, keeps above the clearance corridor at every time, and keeps the speed and acceleration limits, with one-sided bounds at the joins of segments. | `drone_safe` in [the compilation](Verified.lean), from `compute_safe` in [the whole-flight proofs](WholeFlight.lean) |
| Execution without a trap | Called from a ready store of the module with a terrain borrowed below address 8192, under a memory cap of at least 35 pages, the export `compute` returns without a trap a new array that holds the words of `compute`.  The terrain stays borrowed, and `top` rises by at most 2,251,064 bytes.  The module's bytes decode to the module, and the store in which it starts is ready under every memory cap of at most 65,535 pages. | `drone_compute_call` in [the call theorem](VerifiedCall.lean), from `drone_trapFree` and `compute_bound` in [the compilation](Verified.lean) |
| Written file | `build/verified/drone.wasm`, as written, holds `encode compiled.module` and decodes to `compiled.module`. | `drone_file` and `drone_file_decode` in [the file theorems](File.lean) |

The optimality, safety, and execution theorems concern the module's bytes, through the round trip
of the encoder, and the file theorems concern the written file.  The safety theorem concerns the ideal point-mass model of
[the drone verification
report](https://github.com/jsmorph/leanexe-papers/blob/main/paper/drone-verification-report/README.md).
`drone_trapFree` states that entry 18 computes `compute` without a trap whenever `top` can rise by
2,251,064 bytes within the memory cap, the constant that `compute_bound` derives from
`compiled.compute.bound_eq`: `forward` builds at most 63 tables, the `k`-th of `45 (k + 2)` choices
of three words, after the first row of 45 choices, and `output` builds at most 128 words.
`drone_compute_call` states that the store in which the module starts is ready, and the host's
placement of the terrain below address 8192 remains a premise.  Its 35 pages hold the 8192 bytes
below that address and the 2,251,064 bytes of `compute_bound`.  It states no final page count,
because no theorem of the verified compiler bounds the pages to which memory grows, as [the journal
entry](../../devnotes.md#2026-10-30-the-verified-total-theorems-of-the-euler-solvers-and-the-drone-planner)
explains.  The axiom reports of `drone_compute_call` and its lemmas in [the call
theorem](VerifiedCall.lean) name only `propext`, `Classical.choice`, and `Quot.sound`, and [the full
check](../../docs/verified-manual.md#the-full-check) fails on a report that names another axiom.

## Building, running, and testing

[`tests/drone/oracle.sh`](../../tests/drone/oracle.sh) ran a reference implementation of the planner
natively and saved 116 terrains with its output in
[`tests/drone/corpus.txt`](../../tests/drone/corpus.txt) and 1,975 calls of its other functions,
including 138 rows of its forward passes, in [`tests/drone/cases.txt`](../../tests/drone/cases.txt).
[`tests/drone/run.sh`](../../tests/drone/run.sh) runs `build/verified/drone.wasm`, which
`tests/verified/run.sh` writes, in the Wasmtime host on every terrain of the corpus and every call
of the case file, and every output matches the reference word for word.  The corpus includes the
five terrains of the figures in [the drone verification
report](https://github.com/jsmorph/leanexe-papers/blob/main/paper/drone-verification-report/README.md).
`tests/verified/run.sh --cases drone` writes and validates that module and compares it in Wasmtime
with native Lean on the `drone` cases of [the verified cases](../../Verified/Examples/Cases.lean).
The cases call `compute` on the terrains of the corpus, each of which must leave only the host's
terrain and the result allocated, and each other export on terrains, rows, and tables from native
runs of the planner.  [The native driver](../../tests/native/verified.sh) runs the same cases on the
module's translation to C, compiled with CompCert.

```sh
tools/leanrun --timeout 60m lake build Demos.Drone.VerifiedCall LeanExe.Pipeline.FileBytes
tests/verified/run.sh --cases drone
tests/native/verified.sh --module drone
tools/leanrun --timeout 10m lake env lean Demos/Drone/File.lean
build/tools/leanexe-wasmtime-host call build/verified/drone.wasm compute array-u64 \
  array-u64:0,100,50,0
tests/drone/run.sh
```

The commands build the theorems and the support of the file theorems, write and test the module,
check the file theorems against the written file, call the module in the Wasmtime host, and run
the comparison with the reference results, with the setup of [the repository
README](../../README.md#commands).  The terrain has four stations of heights 0, 100, 50, and 0, and
the call prints `[0, 0, 200, 10, 175, 10, 0, 0]`: the altitude and speed at each station.
`tests/drone/oracle.sh` reads the reference implementation from the repository's history with `git
show`, and it has already written the corpus, so it runs only to regenerate the corpus.

## Related examples

[`Euler`](../Euler/README.md) is the other large program whose module has a call theorem without a
trap and a bound on its allocation, and [`Increment`](../../Examples/Increment/README.md) the
smallest.  [`Clob`](../Clob/README.md) has loops over arrays with tuple states at a small scale.
[`Below100`](../../Examples/Below100/README.md) has `LeanExe.repeatWhile`, which the planner's
forward pass also uses.

## References

- R. Bellman, *Dynamic Programming*, Princeton University Press, 1957.
- J. Stephens, [*Verified Terrain-Following Flight Planning in
  LeanExe*](https://github.com/jsmorph/leanexe-papers/blob/main/paper/drone-verification-report/README.md),
  Morphism, September 26, 2026.
