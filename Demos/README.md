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
| [Gate](Gate/README.md) | WASM SPEC WASMF | Chi-square gating and track association: intervals that contain the chi-square distribution function, its tail, and its quantile, an interval that contains the squared Mahalanobis distance of an innovation with a proof that the covariance is positive definite and a verdict against the gate's threshold, and a check of an assignment's dual certificate in `Int64`, with closed-form, enclosure, positive-definiteness, weak-duality, optimality, call, allocation-bound, and compilation proofs. |
| [SGP4](Sgp4/README.md) | WASM SPEC WASMF | Near-Earth SGP4 propagation of catalog element sets: a model over the reals, a binary64 program tested against the reference states, an enclosing program whose intervals provably contain the model's position and velocity, and proved readers of two-line element sets and decimal values. |
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
