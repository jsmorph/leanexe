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
| [Slew](Slew/README.md) | WASM SPEC WASMF C | Attitude slew planning under cone constraints, with safety, premise, NaN-freedom, optimality, allocation-bound, and compilation proofs. |
| [Energy](Energy/README.md) | WASM SPEC WASMF C METAL M7 | Authorization of battery power limits for a solar-and-battery site, with proofs that accepted limits satisfy the modeled energy and grid limits, or stay no further outside a limit than a return to fallback. |
| [Order book](OrderBook/README.md) | WASM SPEC C WASI | Central limit order book of one instrument with price-time priority, with specification, refinement, and call proofs for its module, and a WASI process with exact-output and termination proofs. |

Each guide states its proof premises and run commands.  Euler's recorded outputs are under [the
Euler run data](https://github.com/jsmorph/leanexe-papers/tree/main/data/euler).  The [verified
compiler's examples](../Examples) demonstrate individual language forms, ownership behavior, and
proof procedures.

## Internal references

- [Stream fold](StreamFold/README.md)
