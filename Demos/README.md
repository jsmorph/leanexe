# Application demos

Each demo contains its application definitions, specifications, compilations, proofs, and host
programs.  Shared algorithms come from [the library](../Library/README.md).  The Forms column gives
each demo's compiled forms in the codes of [the algorithm index](../index.md), whose section on
applications names the theorem for each code.

| Demo | Forms | Program and results |
|---|---|---|
| [Euler](Euler/README.md) | WASM SPEC WASMF C CALIGN METAL A64 | Two finite-volume solvers with execution, memory, conservation, admissibility, and numerical bounds. |
| [GPT](Gpt/README.md) | WASM SPEC WASMF C A64 | Binary64 GPT-2, cached generation, causality and cache-equivalence proofs, and sampling. |
| [GPT32](Gpt32/README.md) | WASM SPEC WASMF C CALIGN A64 WGSL PTX | Binary32 GPT-2 with Wasm, WGSL, and PTX compilation and modeled host, dispatch, and launch proofs. |
| [Drone](Drone/README.md) | WASM SPEC WASMF C | Terrain-following flight planning with optimality, flight-safety, and execution proofs. |
| [Running sum](RunningSum/README.md) | WASM SPEC WASI | Decimal cumulative totals over stdin, with a verified WASI process loop and runs in native Lean. |
| [Floating-point running sum](RunningSumFp/README.md) | SPEC WASI | Binary64 cumulative totals over stdin, with parsing, addition, printing, and WASI process proofs. |
| [Conjunction](Conjunction/README.md) | WASM SPEC WASMF | Interval that contains the two-dimensional probability of collision of two space objects, with a verdict against a threshold, and intervals that contain the circular and linear errors at a probability, such as CE90 and LE90, with enclosure, verdict, radius, call, and compilation proofs. |
| [Passive safety](PassiveSafety/README.md) | WASM SPEC WASMF | Authorization of a burn plan for a deputy near a chief in a circular orbit under the Hill–Clohessy–Wiltshire model, with proofs that the closed form solves the equations and is their unique solution, and that an accepted plan keeps every trajectory from a box of initial states and of burn errors, with every burn executed or any one burn missed, at or above a separation bound over a horizon and a radial and cross-track bound for all time after its last burn. |
| [Attitude](Attitude/README.md) | WASM SPEC WASMF | TRIAD attitude determination from two vector observations: intervals that contain TRIAD's matrix, and a deterministic bound on the angle between every matrix in them and the true attitude for bounds on the observations' errors, with proofs of TRIAD's properties over the reals, the enclosure, the bound, its link to the slew planner's `ε`, and the compilation. |
| [SGP4](Sgp4/README.md) | WASM SPEC WASMF | Near-Earth SGP4 propagation of catalog element sets: a model over the reals, a binary64 program tested against the reference states, an enclosing program whose intervals provably contain the model's position and velocity, and proved readers of two-line element sets and decimal values. |
| [Initial orbit determination](Orbit/README.md) | WASM SPEC WASMF | Gibbs' method over boxes of three positions and Lambert's problem for zero revolutions in Izzo's formulation over boxes of two positions, with proofs that Gibbs' formula gives the velocity of a two-body orbit, that Izzo's time of flight decreases strictly and takes each positive value once, that the returned intervals contain the model's values, and that the modules compute the programs. |
| [Screening](Screening/README.md) | WASM SPEC WASMF | Conjunction screening of two objects on Kepler orbits: an apogee–perigee filter and an orbit-path filter that exclude only pairs that never come within the threshold, and intervals of time that hold every close approach of a window, with proofs of the filters, the isolation, the padding for trajectories near the Kepler ones, and the module's call. |
| [Avoidance](Avoidance/README.md) | WASM SPEC WASMF | Authorization of an impulsive avoidance burn against listed conjunctions: intervals that contain the two-dimensional probability of collision after every velocity change of a box of execution error, from the two-body change of the trajectory by the burn and the straight-line encounter, with proofs that the propagation solves Newton's equation, that the miss vector is the closest approach of the relative motion, that an accepted burn's probability lies below the threshold for every conjunction, and of the module's calls. |
| [Slew](Slew/README.md) | WASM SPEC WASMF C | Attitude slew planning under cone constraints, with safety, premise, NaN-freedom, optimality, allocation-bound, and compilation proofs. |
| [Energy](Energy/README.md) | WASM SPEC WASMF C METAL M7 | Authorization of battery power limits for a solar-and-battery site, with proofs that accepted limits satisfy the modeled energy and grid limits, or stay no further outside a limit than a return to fallback. |
| [Order book](OrderBook/README.md) | WASM SPEC C WASI | Central limit order book of one instrument with price-time priority, with specification, refinement, and call proofs for its module, and a WASI process with exact-output and termination proofs. |
| [BMS protection](Bms/README.md) | WASM SPEC M7 | Protection layer of a battery management system for four lithium iron phosphate cells, with a machine that answers each framed record of a bridge with relay permits, proofs that a nonzero permit follows a reset acceptance, a start, and records that pass every check, and that `NORMAL` follows the precharge condition, and a Cortex-M7 image whose answers, from reset, are the machine's, run on the board through a fault-injection schedule. |
| [Ranked-choice tabulation](Rcv/README.md) | WASM SPEC WASMF C WASI | Instant-runoff tabulation under Oakland City Charter §1105.  A module, a WASI process, and a C translation return the specification's report of a canonical ballot file, with proofs of the reader, the rounds, the relations to a count without batches and to Alameda County's practice, and properties of instant runoff.  The module's count of the 2022 contest for School Director, District 4, gives the figures of the County's corrected report, and a Python script reproduces the County's first certified figures under its faulty setting.  A second module counts contests under Maine's 21-A M.R.S. §723-A in the same forms, with the same kinds of proofs. |

Each guide states its proof premises and run commands.  Euler's recorded outputs are under [the
Euler run data](https://github.com/jsmorph/leanexe-papers/tree/main/data/euler).  The [verified
compiler's examples](../Examples) demonstrate individual language forms, ownership behavior, and
proof procedures.

## Internal references

- [Stream fold](StreamFold/README.md)
