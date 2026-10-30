# Application demos

Each demo contains its application definitions, specifications, compiler modules, proofs, and host
programs.  Shared algorithms come from [the library](../Library/README.md).  The Forms column gives
each demo's compiled forms in the codes of [the algorithm index](../index.md), whose section on
applications names the theorem behind each code.

| Demo | Forms | Program and results |
|---|---|---|
| [Euler](Euler/README.md) | L V S C A B | Two finite-volume solvers with execution, memory, conservation, admissibility, and numerical bounds. |
| [GPT](Gpt/README.md) | L V S F C | Binary64 GPT-2, cached generation, causality and cache-equivalence proofs, and sampling. |
| [GPT32](Gpt32/README.md) | V S C A G | Binary32 GPT-2 with Wasm and WGSL compilation and modeled host and dispatch proofs. |
| [Drone](Drone/README.md) | L V S C | Terrain-following flight planning with optimality, flight-safety, and execution proofs. |
| [Clob](Clob/README.md) | L V S C | Order book with command-stream and compilation proofs. |
| [Running sum](RunningSum/README.md) | V S I | Decimal cumulative totals over stdin, with a verified WASI process loop and runs in native Lean. |
| [Floating-point running sum](RunningSumFp/README.md) | S I | Binary64 cumulative totals over stdin, with parsing, addition, printing, and WASI process proofs. |
| [Slew](Slew/README.md) | V S F C | Attitude slew planning under cone constraints, with safety, premise, NaN-freedom, optimality, allocation-bound, and compilation proofs. |

Each guide states its proof premises and run commands.  Euler's recorded outputs are under
[the Euler run data](https://github.com/jsmorph/leanexe-papers/tree/main/data/euler).  The [compiler examples](../Examples) demonstrate individual
language forms, ownership behavior, and proof procedures.
