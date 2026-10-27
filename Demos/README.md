# Application demos

Each demo contains its application definitions, specifications, compiler modules, proofs, and host
programs.  Shared algorithms come from [the library](../Library/README.md).

| Demo | Program and results |
|---|---|
| [Euler](Euler/README.md) | Two finite-volume solvers with execution, memory, conservation, admissibility, and numerical bounds. |
| [GPT](Gpt/README.md) | Binary64 GPT-2, cached generation, causality and cache-equivalence proofs, and sampling. |
| [GPT32](Gpt32/README.md) | Binary32 GPT-2 with Wasm and WGSL compilation and modeled host and dispatch proofs. |
| [Drone](Drone/README.md) | Terrain-following flight planning with optimality, flight-safety, and execution proofs. |
| [Clob](Clob/README.md) | An order book with command-stream and compilation proofs. |
| [Running sum](RunningSum/README.md) | Decimal cumulative totals over stdin, with a verified WASI process loop and native execution. |
| [Floating-point running sum](RunningSumFp/README.md) | Binary64 cumulative totals over stdin, with parsing, addition, printing, and WASI process proofs. |
| [Slew](Slew/README.md) | A slew planner for a spacecraft under cone constraints, with safety, NaN-freedom, optimality, memory-bound, and compilation proofs. |

Each guide states its proof premises and run commands.  Euler's recorded outputs are under
[the Euler run data](../data/euler).  The [compiler examples](../Examples) demonstrate individual
language forms, ownership behavior, and proof procedures.
