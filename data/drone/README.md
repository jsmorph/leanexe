# Terrain-following drone flight plans

The drone planner computes a flight over up to 64 stations of terrain, 100 units apart, with
heights from 0 to 1,000,000.  At each station the drone is in one of 45 states, 9 altitudes 25
apart above the station's floor and 5 horizontal speeds from 0 to 20, and the planner finds the
admitted flight of least duration, with the altitude above the floors as the second criterion.
The output is the altitude and speed at each station, from rest on the ground at the first
station to rest on the ground at the last.  This branch rewrites main's program in its dialect,
compiles it, proves that the bytes compute the rewrite, and proves main's optimality and flight-safety theorems
about the rewrite.

## Program and proofs

[The planner](../../LeanExe/Examples/Drone.lean) uses `UInt64` words throughout and replaces
main's recursions on fuel with counted loops: the square root takes 17 halvings, a row is a build
over the 45 targets of loops over the 45 sources, the forward pass carries one table of all rows,
and the output follows the parents back from the last station.  [The module
definition](../../Project/Drone/Module.lean) compiles it into a 5,181-byte module, `drone.wasm`,
with SHA-256 `c6dc196215e4302d7e1560b36f72c577a9b1984b1173fa4f98487d1078fb7123`.  The proofs are
in [`Project/Drone`](../../Project/Drone/), and they use only `propext`, `Classical.choice`, and `Quot.sound`.

| Claim | Statement | Theorem |
|-------|-----------|---------|
| Optimality | The module's bytes decode to a module whose `compute` export returns the words of the Lean function `compute`, or stops at `unreachable`.  For terrain within the bounds, those words have two per station and encode an admitted flight, and no admitted flight from rest at the first station to rest at the last has a smaller (duration, excess) cost.  Empty or invalid terrain gives `#[]`. | `drone_compute` in [the bytes theorems](../../Project/Drone/Verify.lean), from `compute_correct` in [the output proofs](../../Project/Drone/Correct.lean) |
| Flight safety | For terrain within the bounds, the point-mass trajectory that the words define departs and arrives on the ground at rest, keeps above the clearance corridor at every time, and keeps the speed and acceleration limits, with one-sided bounds at the joins of segments. | `drone_safe` in [the bytes theorems](../../Project/Drone/Verify.lean), from `compute_safe` in [the whole-flight proofs](../../Project/Drone/WholeFlight.lean) |
| Complete execution and memory | Called with any terrain that an allocator with no free block has placed below address 8192, under a memory cap of at least 70 pages, the export returns the words of `compute` without stopping at `unreachable` and ends with at most 70 pages (4.375 MiB) of linear memory. | `drone_compute_total` in [the total-execution theorems](../../Project/Drone/Total.lean) |

Main proved the optimality and safety theorems about its source program and the execution
theorem about a Lean model of its compiled module, with at most 1,024 pages, and no theorem of
main connects that model to the bytes.  Here every theorem concerns the bytes, through the round
trip of the encoder.  The safety theorem concerns the ideal point-mass model of main's report,
and the allocator state of the total theorem is a hypothesis, which no theorem connects to the
module's instantiation.

## Tests

[`tests/drone/oracle.sh`](../../tests/drone/oracle.sh) ran main's program (commit `188ccb4d`) natively once and saved 116
terrains with main's output in [`tests/drone/corpus.txt`](../../tests/drone/corpus.txt) and 1,975 calls of main's other functions,
including 138 rows of main's forward passes, in [`tests/drone/cases.txt`](../../tests/drone/cases.txt).  [`tests/drone/run.sh`](../../tests/drone/run.sh)
runs `drone.wasm` in the Wasmtime host on all of them, and every output matches main's word for
word.  The five terrains of the figures in [main's report](../../paper/drone-verification-report/README.md),
whose outputs main saved in [`evidence/runs.json`](../../paper/drone-verification-report/evidence/runs.json), return the same words from `drone.wasm`.

```sh
tests/drone/oracle.sh      # once: the corpus from main's program
tests/drone/run.sh         # drone.wasm against the corpus
tests/modules/run.sh       # the module cases, drone included
```

[Main's report](../../paper/drone-verification-report/README.md) describes main's development:
its compiler, its generated model of the binary, and its proof.  It is kept as the record of that
work, and this README describes the program and theorems of this branch.
