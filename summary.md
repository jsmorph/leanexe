# LeanExe Technical Summary

LeanExe compiles a restricted, first-order subset of Lean 4 to standalone WebAssembly.  Lean serves as the source language, type checker, and proof environment.  The compiler loads a checked declaration from a built Lake module, classifies its reachable call graph against the accepted subset, lowers it through a small typed IR, and emits a WASM module with an arena allocator and reference-counted heap but no Lean runtime.  The compiler workspace pins Lean 4.29.1, while the Talos proof workspace pins Lean 4.31.0.  This document describes architecture; [Developing LeanExe](DEVELOPING.md) owns development procedure, and the [Development Plan](plan.md) owns current work.

## Compilation Pipeline

Compilation begins in `LeanExe/Extract/Env.lean`, which imports the requested module from `.lake/build/lib/lean` and resolves the entry declaration.  `LeanExe/Extract/Core.lean` collects every reachable declaration from the entry, restricted to the entry's root namespace, and distinguishes three roles established in `LeanExe/Extract/Types.lean`: entry functions with public ABI signatures, internal functions with internal layouts, and inline-only helpers that specialize away at call sites.  A scan over collected bodies discovers synthetic functions for Lean's generated recursion machinery, such as `brecOn` structural recursion, `WellFounded.fix` shapes, and closed structural folds, recognized by `LeanExe/Extract/StructuralRec.lean` and `LeanExe/Extract/Patterns.lean`.

Extraction runs in two passes.  The first pass computes skeleton ownership information, in particular the fresh-owner offsets of helper-call results, and the second pass re-extracts every function with complete ownership summaries so release statements are placed correctly.  `LeanExe/Extract/Demand.lean` provides a demand analysis over Lean expressions, tracking which parameters an expression may evaluate, must evaluate, and whether it may trap; this analysis gates laziness and evaluation-order decisions during lowering.  `LeanExe/Extract/Values.lean` and `LeanExe/Extract/Storage.lean` handle value representation: liveness, owner slots, child-pointer masks, and the flattening of structures, tagged values, products, and heap references into fixed-width `i64` slot sequences.

The target of extraction is the first-order core IR in `LeanExe/IR/Core.lean`.  Its type language covers scalars, bounded `Nat`, byte arrays, arrays, products, sums, structures, variants, and recursive variants.  Its expression and statement forms cover locals, 64-bit arithmetic, conditionals, lets, calls, traps, heap and array allocation with slot layouts, slot loads, release statements, loops, and a family of multi-slot fold constructs for arrays, byte arrays, ranges, and general loops.  The IR carries its own reference interpreter (`Expr.eval`, `Stmt.eval`), which gives the IR an executable semantics independent of the WASM backend.

`LeanExe/Wasm` holds the backend: `Instr.lean` defines the instruction model, `Binary.lean` carries the module model, binary encoder, embedded runtime, and WASI command adapters, and `Wat.lean` prints the text format.  The backend uses the LEB128 functions in `LeanExe/Wasm/Leb.lean`, which LeanExe can compile and execute as one of its own artifacts.  Exact file sizes are omitted because they change without altering the architecture.

| Module | Role |
|--------|------|
| `LeanExe/Extract/Core.lean` | Extraction mutual block: value, condition, and primitive lowering; recursion shapes; two-pass driver. |
| `LeanExe/Extract/Values.lean` | Binding lookup, primitives, liveness, and ownership. |
| `LeanExe/Wasm/Binary.lean` | WASM module model, binary encoder, runtime, and WASI adapters. |
| `LeanExe/Extract/Types.lean` | Type recognition, signatures, and entry and inline classification. |
| `LeanExe/Extract/Demand.lean` | May-evaluate, must-evaluate, and may-trap demand analysis. |
| `LeanExe/Extract/Patterns.lean` | Matcher decoding and monad recognition. |
| `LeanExe/Extract/StructuralRec.lean` | Structural-recursion recognition and closed folds and predicates. |
| `LeanExe/Extract/Storage.lean` | Heap loads, field flattening, and parameter bindings. |
| `LeanExe/IR/Core.lean` | Core IR types and reference interpreter. |
| `LeanExe/Extract/OwnershipReport.lean`, `Report.lean` | Extraction and ownership diagnostics. |

## Accepted Language

The subset, specified in [Language Specification](spec.md) and taught in [LeanExe User Manual](manual.md), covers pure, monomorphic, first-order programs.  Supported values include `Unit`, `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, `ByteArray`, `LeanExe.AsciiString`, arrays, products, user structures and inductives, `Option`, `Except`, monomorphic self-recursive inductives, mutual recursive families, and monomorphic recursive instances such as `List α` over supported element layouts.  Recursive data works internally, including inside arrays and fixed-width structures, but cannot cross the public ABI.  Control flow covers `let`, calls, `if`, pattern matching, pure `do` blocks with mutable locals through `Id.run`, `for` and `while` loops in `Id`, `Option`, and `Except`, `Nat`-fuel tail recursion, direct and mutual structural recursion in the recognized generated shapes, closed structural folds and predicates, and a set of direct-lambda `List` and `Array` library calls that specialize to first-order code.  Type-class evidence is accepted when Lean resolves the instance statically and a bounded normalizer reduces method projections to first-order expressions, per [Type Classes](typeclasses.md).

Rejection is a first-class outcome.  The `report` command classifies the entry and every reachable dependency and prints exact reasons, and the plan treats a precise failure as preferable to unsound output.  Runtime `String` and `Char`, higher-order values that survive normalization, runtime class dictionaries, full `IO`, `unsafe`, `partial`, unbounded `Nat` arithmetic, course-of-values recursion, and public recursive data all remain outside the language even when Lean accepts the source.

## Memory Model and Runtime

Generated modules use one linear memory with an arena allocator that grows memory when neither the free list nor the current heap range can satisfy a request.  Each heap object carries a header with a magic byte, a kind tag distinguishing raw byte buffers, slot records, and arrays, and a reference count.  Slot records and arrays carry child-pointer masks marking which slots hold owned heap references, so releasing a root follows recursive-inductive child pointers, `ByteArray` owner slots, and nested `Array` owner slots.  Every module exports `memory`, `alloc(len : i64) : i64`, `reset`, `retain`, `release`, and `free`, and compiled code can read `allocCount`, `retainCount`, `releaseCount`, and `freeCount` through `LeanExe.Runtime`.

The compiler inserts releases conservatively.  It releases local heap temporaries only when the owner is nonrecursive (`ByteArray` or `Array`) and provably a fresh allocation or fresh helper result, and it releases replaced heap-valued fold and loop accumulators after the first iteration when the replacement is proven fresh.  Recursive heap temporaries may leak rather than risk an unsound release.  Source code can mark explicit ownership boundaries with `LeanExe.Runtime.release`, which the extractor preserves; the safety condition on that call (no live alias uses the released value) is documented but not yet proved by the compiler.  The `ownership-report` command exposes result owner slots, fresh-owner offsets, emitted releases, and accumulator release offsets for inspection.

## ABI and Command Modes

Scalars cross the public boundary as single `i64` values, with `UInt8` and `UInt32` normalized modulo their width.  `ByteArray` uses a pointer-length pair, structures flatten field-by-field, nonrecursive inductives flatten to a tag plus payload slots, and arrays pass as a pointer to fixed-width-slot elements.  A host writes inputs through `alloc` and the exported memory, and it reads heap results before calling `release` or `reset`.  The repository includes a C host runner, `tools/wasmtime-host.c`, built against the Wasmtime C API for ABI-level tests that need memory writes and inspection.

The `lean-wasm` CLI provides library-mode compilation and five WASI Preview 1 command adapters, none of which compile Lean `IO`: the entry stays a pure function and the generated `_start` performs the bounded I/O.

| Command | Entry type | Behavior |
|---------|-----------|----------|
| `compile`, `compile-wat` | any accepted entry | Library-mode WASM or WAT with runtime exports |
| `report`, `ownership-report` | any declaration | Subset classification; ownership and release diagnostics |
| `dump-ir` | any accepted declaration | Extracted IR for lowering, evaluation-order, trap, and release inspection |
| `eval-ir` | scalar entry in the reference-interpreter fragment | Executes the extracted IR without the WASM backend |
| `compile-wasi` | `ByteArray` | Writes the result to stdout through `fd_write` |
| `compile-wasi-stdin` | `ByteArray -> ByteArray` | Bounded stdin transform to stdout |
| `compile-wasi-stdin-except` | `ByteArray -> Except ByteArray ByteArray` | Ok to stdout; error to stderr with `proc_exit 1` |
| `compile-wasi-argv-except` | `Array ByteArray -> Except ByteArray ByteArray` | Bounded argv with the same error protocol |
| `compile-wasi-stdin-argv-except` | `ByteArray -> Array ByteArray -> Except ByteArray ByteArray` | Bounded stdin plus argv |

The CLI also retains commands from the original closed prototype (`emit`, `wat`, `eval`, `collatz-eval`, `collatz-bench`, and the static `report --out` text), which predate the generic extraction path.

## Verification

Assurance is staged, per the correctness strategy in the [Development Plan](plan.md).  Differential testing is built and routine.  `test/run_all.js` runs report classification, ownership reports, a guard that no JavaScript instantiates WASM directly, core correctness, reference counting, byte-array allocation, ASCII strings, the integer-map example, JSON programs, WASI programs, self-emission, randomized comparison, IR comparison, and standard-Lean comparison tests; exact run totals belong in the [Development Journal](devnotes.md).

`tools/compare-standard.js` is the differential harness.  It generates a temporary standard Lean runner, executes it with `lake env lean --run`, compiles the same entry through LeanExe, runs the artifact under Wasmtime, and compares results.  Command modes compare exit status, stdout, and stderr byte-for-byte.  Pure mode compares scalar exports through `wasmtime --invoke`; pure-ABI mode decodes heap-backed results from exported memory through the C host runner and JSON layout descriptors from `tools/abi_layout.js`; pure-bytes mode serializes a pure result to bytes and compares through a generated WASI wrapper.

Artifact verification lives in the Talos proof workspace at `proofs/talos-gcd`, described in the workspace [README](proofs/talos-gcd/README.md).  LeanExe emits WASM, `wasm-tools print` renders WAT, Talos decodes the WAT into a Lean module value in a generated `Program.lean`, and a handwritten `Spec.lean` proves a theorem about the decoded module.  Fourteen proofs cover scalar algorithms, recursive data, byte processing and allocation, exact runtime accounting, the self-compiled unsigned LEB128 encoder, and the CLOB quote and cancel exports; the proof README gives each theorem's exact scope.

The workspace organizes the artifacts around a shared proof library.  The four runtime functions every module ships are pinned to shared definitions by `rfl` checks, and their behavior is proved generically over the module and function index.  A generic teardown theorem, `release_frees_tree`, covers recursive release of slots-kind ownership trees, while shared tactics handle read-over-write and address-normalization goals.  The scripts `tools/check-talos*.sh` recompile each source entry, compare fresh WASM and WAT with the checked-in proof inputs, and rebuild the proofs.  [Verifying a Program](verifying.md) documents the complete procedure.

## Documentation

The [Language Specification](spec.md) defines the accepted subset, ABI, memory management, numeric semantics, and unsupported behavior.  The [LeanExe User Manual](manual.md) teaches source patterns and diagnostics, while [Developing LeanExe](DEVELOPING.md) defines setup, local gates, generated files, and troubleshooting.  [Talos Proofs](proofs/talos-gcd/README.md) owns the current theorem inventory, [Verifying a Program](verifying.md) owns the proof procedure, the [Development Plan](plan.md) owns future work, and the [Development Journal](devnotes.md) owns history and test records.  The old [Development Agenda](agenda.md) is archived, and the two `leanexe-talos` documents are marked as historical experiments.

## Current State and Observations

Several structural facts govern further work.  Extraction remains concentrated in the large mutual block in `LeanExe/Extract/Core.lean`, despite the surrounding module splits.  Artifact comparison is byte-exact, so a semantically neutral code-generation change can move every proof input; the runtime lemma library reduces the resulting proof work, but generated `Program.lean` models and entry proofs still track the bytes.  The gap between the Talos WASM model and Wasmtime execution remains a trusted-base assumption.  The compiler releases constructor fields, fold sources and accumulators, and owned temporaries in supported positions, but it does not check the source-level ownership precondition for `LeanExe.Runtime.release`.  The formal stages between differential testing and artifact proofs, including `extract_correct`, verified IR passes, and a general `wasm_lower_correct`, have no proof development in this repository.
