# Module Guarantees and the Road to Them

This document lists the guarantees a user of a compiled module should get, states where each stands, and fixes the order of work that produces the rest.  It is the target that the [emitter restructuring](emitter.md) and the [compiler verification plan](../proofs/talos/compiler-verification.md) serve.  Each phase of that work fills rows in the table below.

## Guarantee Sheet

| Guarantee | State | Notes |
|-----------|-------|-------|
| Result equals the source function on valid input | Proved | Per artifact, twenty cases, input-generic. |
| Termination on valid input | Proved | `TerminatesWith` in every artifact theorem. |
| Writes confined to the module's heap and declared outputs | Proved inside theorems | Byte-frame conditions; a user-facing restatement is planned. |
| No imports, therefore no I/O and no host callbacks | True structurally | A theorem stating it is planned; the check is decidable. |
| Determinism: equal inputs give equal outputs | Follows from the model | The code reads nothing from the environment; a restatement is planned. |
| No division trap | Unproved | Planned; WASM traps on unsigned division by zero and the IR uses it. |
| Arithmetic is modular; natural-number readings hold under stated bounds | Proved | Per artifact, with explicit no-overflow side conditions. |
| Exact final heap top | Proved | Stated in each artifact theorem's allocator globals. |
| Peak heap bound | Implied | The no-grow fit premise under fixed pages is a peak bound; a compiler-computed budget function is planned. |
| Stack depth bound | Not stateable | The model does not count call frames; needs model instrumentation. |
| Worst-case step count per call | Latent | Fuel is a step count; making the bound explicit is planned. |
| Defined behavior on invalid input | Not covered | Theorems cover success paths only; planned as defined rejection or a modeled trap with confinement. |
| Constant memory across repeated calls | False today | Bump-only programs leak by design; requires a compiler change (reset or reuse), then a steady-state theorem. |
| Domain properties (conservation, price-time priority, book invariants) | Partly proved | Conservation for `matchFuel`, first-index priority for `findBest`; per program. |
| Host assumptions: ABI layout, memory pages, initial globals, stack size | Assumed | Documented premises; checked only by differential execution. |

## Order of Work

1. Finish the proof-infrastructure overhaul and close the aggregate and execution gates.  In progress.
2. The interpreter package is third-party: it lives in the Talos repository, pinned by commit.  The model therefore cannot be instrumented in place.  The plan of record is a shadow interpreter in the proof workspace: a fuel-based variant of the Talos `run` that additionally counts frame depth and a heap watermark, with one agreement theorem proving it returns what `run` returns.  Cost claims attach to the shadow; the pinned dependency never changes.  A maintained fork is the fallback if the agreement proof proves infeasible.
3. Do the [emitter restructuring](emitter.md).  The structured output is the input for every static analysis: stack depth, operand depth, call graph, allocation costs.
4. Build the shadow interpreter and its agreement theorem: step count, frame depth, and a heap watermark in one cost semantics serving the time, stack, and heap rows together.
5. In parallel, state the cheap guarantees that need no new machinery: confinement, no imports, determinism, no division trap.  These are restatements or small additions to existing theorems.
6. Run the compiler-verification phases with cost fields in the emitter templates from the start.  After this, every new program receives the full guarantee set automatically.
7. Change the allocator to reset or reuse between calls, then prove the steady-state theorem.  The current leak is a fact about the generated code, and no theorem improves it.

## Reading the Table

"Proved" means a machine-checked theorem exists in the proof workspace.  "Planned" and "latent" mean the machinery exists and the statement does not.  "Assumed" means the claim is a premise the host must satisfy, checked only empirically.  The table should change in exactly one direction; a row moving away from "proved" is a regression and belongs in the journal.
