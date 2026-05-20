# Development Journal

## 2026-05-20: Parked Ownership Diagnostics

The next ownership follow-up should be diagnostic.  A proposed `lean-wasm ownership-report --module M --entry E` command should print, per extracted function, the result type, result owner slots, helper-result fresh-owner offsets, compiler-inserted releases, returned owner slots kept live, fold accumulator release offsets, and explicit `LeanExe.Runtime.release` sites.  Snapshot cases should include `byteArrayResultDropsOwnedTempStats`, `u64ListTailValue`, `JsonTreeCommand.makeTree`, and a fold-accumulator release case.

Broader recursive heap-result cleanup should wait for explicit provenance.  The compiler needs enough data to prove whether returned recursive roots own their children or borrow from a temporary, including arrays and byte-array owners inside the graph.  The current conservative recursive boundary is deliberate: nonrecursive result cleanup, accumulator releases, helper-result summaries, and source-level release boundaries cover the cases the compiler can justify today.

This note parks the memory-management topic so the next work can return to language expressiveness.  The most useful next target is broader Lean source support for local mutable-state style through checked `Id.run` and `do` forms.  That target would make parser, scanner, and command-transform examples shorter without adding runtime services.

## 2026-05-20: Nonrecursive Heap-Result Temporary Release

Heap-returning functions now have a limited compiler-emitted release path for dead nonrecursive heap temporaries.  During result materialization, the extractor protects owner slots that appear in the returned heap value, owner slots reached through borrowed root expressions, and heap arguments to returned helper-call results that may borrow from those arguments.  It may release a fresh nonrecursive owner slot, currently an internal `ByteArray` or `Array` owner, when that owner is absent from the protected set and the body has not already released it.

The implementation excludes recursive heap-result temporaries.  A broader recursive rule exposed unsound releases in existing JSON tree programs, where returned recursive values can contain borrowed children, arrays, and byte-array owners whose lifetime depends on retain and ownership-transfer details across several layouts.  Recursive heap temporaries still release in scalar-result functions, helper-result scalar callers, fold and loop accumulator replacement, and explicit source-level `LeanExe.Runtime.release` boundaries.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 25 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 638 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 49 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 638 accepted, 29 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 49 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Fold Accumulator Ownership Release

Loop-carried heap values now have a conservative compiler-emitted release path.  The extractor computes owner-slot offsets for the accumulator result type, including owner slots inside products, structures, sums, and nonrecursive tagged payloads.  It attaches a release offset to an `Array.foldl`, `ByteArray.foldl`, or accepted pure `for` loop only when the staged next accumulator slot is proven fresh by local allocation analysis and the body has not already released the old accumulator slot.

The WASM emitter now evaluates the loop body, stages the next accumulator slots, evaluates the loop-exit flag, releases the previous iteration's owned accumulator roots, and then copies staged values over the accumulator locals.  A loop releases a shared root only once when two owner slots hold the same pointer.  It skips the initial accumulator value, because ordinary Lean aliases can still refer to that value after the loop and the compiler does not yet prove that the initializer is unique.  This rule reclaims the common immutable-update pattern used by byte-array accumulators, array accumulators, and recursive-inductive accumulators without requiring source-level `LeanExe.Runtime.release` in the loop body.

The release rule remains local to supported loop and fold accumulator replacement.  Escaping heap-pointer results stay owned by the caller or host, and helper results that may borrow from heap arguments stay conservative unless the existing ownership-summary pass proves the relevant owner slot fresh.

Checks run:

- [x] `lake build LeanExe.Wasm.Binary` returned successfully.
- [x] `lake build lean-wasm` returned successfully.
- [x] `lake build LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 636 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/refcount.js` returned `checked 24 refcount cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 636 accepted, 29 rejected, and 13 trapped cases`, `checked 24 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Recursive Child Ownership Transfer

Recursive heap allocation now carries an owned-child mask in addition to the child-pointer mask.  The child-pointer mask still tells `release` which slots contain heap children, while the owned-child mask tells allocation which child pointers are already owned by the newly allocated parent.  Allocation retains child pointers that are borrowed and skips the retain for child pointers proven fresh by local allocation analysis or helper-result ownership summaries.

This makes recursive helper-result cleanup sound for scalar-result callers.  A helper may receive a recursive heap value, return a fresh recursive value that embeds both a fresh child and a borrowed input child, and the caller may release the temporary result after scalar traversal.  The refcount test covers that shape with a small binary tree and checks that all three recursive heap blocks become reusable.

The WASI tree examples exposed the matching source-level rule.  Immutable insertion shares untouched subtrees with the previous accumulator, so correct RC must retain those children and the old accumulator root must be released after replacement when the program owns that accumulator.  The extractor now preserves `let _ := LeanExe.Runtime.release value` as an ownership boundary, `JsonTreeCommand` uses that form when inserting into an owned accumulator, and the WASI tests check that explicit releases advance free counters without assuming that release and free counts are equal under sharing.

Checks run:

- [x] `lake build LeanExe.Extract.Core` returned successfully.
- [x] `lake build lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 17 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 631 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 631 accepted, 29 rejected, and 13 trapped cases`, `checked 17 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Helper Result Ownership Summaries

The release pass now has per-helper ownership summaries for fresh array and byte-array result owner slots.  The compiler first extracts the reachable functions without summaries, computes a fixed-point summary over the extracted IR, then extracts again with those summaries available to the existing release insertion paths.  This removes the old rule that suppressed helper-call cleanup whenever a callee had any heap-bearing parameter.

The summary pass starts with parameters unowned, follows assignments, local lets, helper calls, branches, releases, and simple loops conservatively, and marks a result owner slot only when the result expression is fresh on every path.  At this checkpoint it applied to array and byte-array owner offsets, including structured results that contain those owners.  The later recursive child ownership work extended the same summary path to recursive-inductive result slots.

Checks run:

- [x] `lake build LeanExe.Extract.Core` returned successfully.
- [x] `lake build lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 16 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 629 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 629 accepted, 29 rejected, and 13 trapped cases`, `checked 16 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Internal Array Owner Slots

Internal `Array α` values now carry two slots: an owner root and the visible array pointer.  The public ABI remains one array pointer, and public or WASI-adapter arrays enter compiled code with owner `0`.  Nested arrays stored inside fixed-width values now have enough ownership metadata for release to follow them without treating borrowed public arrays as owned roots.

The array child mask now marks nested `Array` owner slots in the same way it marks `ByteArray` owners and recursive-inductive child pointers.  Array-copying operations retain nested-array owners when they share elements, while operations that insert freshly constructed arrays transfer the owned root into the new array.  Array operations that can return the original input preserve the original owner slot, so no-op updates over borrowed public arrays remain borrowed.

The extractor no longer treats an arbitrary scalar as a complete array value during materialization.  Array values must carry owner and pointer slots, which exposed and fixed `Array.swapAt`'s updated-array result.  Local materialization also has a specific owned-array path to avoid creating an alias that would be released twice after an explicit `LeanExe.Runtime.release`.  The WASI argv adapters now pass owner `0` plus the visible array pointer to entries that accept `Array ByteArray`.

Checks run:

- [x] `lake build lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 11 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 614 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 614 accepted, 29 rejected, and 13 trapped cases`, `checked 11 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Heap-backed Equality Lowering

Equality lowering now includes `ByteArray` and fixed-width `Array α` values when `α` also has supported equality.  `ByteArray` equality binds both pointer-length pairs once, compares lengths first, and then scans bytes in order.  Array equality binds both array pointers once, compares lengths first, loads each element into compiler-managed local slots, and evaluates the same type-directed structural equality expression used for standalone values.

The implementation keeps recursive-inductive equality rejected.  Arrays of recursive-inductive elements therefore remain outside supported equality, even though recursive values can still appear in internal arrays for traversal and storage.  Supported array equality covers scalar elements, nested arrays, byte-array elements, structures containing byte arrays, and nonrecursive tagged values whose payload fields all support equality.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 610 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 38 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 610 accepted, 29 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStructureArrayEquality --out /tmp/byteArrayStructureArrayEquality.wat` returned successfully.
- [x] `build/tools/wasmtime/current/wasmtime --invoke byteArrayStructureArrayEquality /tmp/byteArrayStructureArrayEquality.wat` returned `1`.

## 2026-05-15: Recursive Pure Result Comparisons

The standard Lean comparison self-test now exercises heap-shaped pure results through `pure-bytes`.  `LeanExe.Examples.Correctness` defines small source-level serializers for a custom recursive list, ordinary `List UInt64`, an array-child tree, a binary tree, and a mutual-recursive JSON-like value.  The comparison tool now serializes producer results for custom-list tail selection, `List` append, reverse, map, and filter, tree construction, binary-tree construction, and mutual-recursive object construction, then compares those bytes against standard Lean.

The self-test also compares the real JSON AST parser as a pure value producer.  The case calls `LeanExe.Ascii.Json.parseBytes` on a nested object, serializes `some value` through `LeanExe.Ascii.Json.render`, and compares the rendered bytes with the WASM wrapper output.  This gives standard-Lean coverage for a recursive AST result without depending on JavaScript heap inspection.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node tools/compare-standard.js --self-test` returned `checked 33 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 31 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 33 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Serialized Pure Standard Lean Comparison

`tools/compare-standard.js` now supports `pure-bytes` mode for concrete pure calls whose results need byte-level serialization.  The tool generates a temporary Lean wrapper under `LeanExe/StandardCompare`, compiles that wrapper with `compile-wasi`, runs the resulting WASI command with Wasmtime, and compares stdout and stderr with a standard Lean runner that evaluates the same serializer.  The serializer sees the target result as `__leanexeValue` and must produce `ByteArray`, so heap-backed results can be compared without adding JavaScript-specific memory inspectors for each source type.

The self-test covers `ByteArray` returns, branch-selected byte arrays, structures containing arrays, structures containing arrays of structures, and byte-producing state structures returned by array and byte-array folds.  The array serializers use `Array.foldl` rather than unchecked indexing, which keeps the generated wrapper inside ordinary Lean source and avoids adding artificial `Inhabited` instances to example types.  `LeanExe/StandardCompare` is ignored because failed comparison runs may leave generated wrapper sources for diagnosis.

At this checkpoint, the correctness fixtures included valid Lean programs that compared unsupported heap-backed values: `Array UInt64`, `ByteArray`, and a recursive inductive.  Each case reached the extractor and failed with an explicit unsupported-equality diagnostic.  The later heap-backed equality work superseded the array and byte-array part of this boundary, while recursive inductive equality remains rejected.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectArrayEquality --out /tmp/rejectArrayEquality.wasm` rejected with `unsupported equality type: LeanExe.IR.Ty.array (LeanExe.IR.Ty.u64)`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectByteArrayEquality --out /tmp/rejectByteArrayEquality.wasm` rejected with `unsupported equality type: LeanExe.IR.Ty.byteArray`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectRecursiveInductiveEquality --out /tmp/rejectRecursiveInductiveEquality.wasm` rejected with `unsupported equality type: LeanExe.IR.Ty.recVariant`.
- [x] `node test/core_correctness.js` returned `checked 596 accepted, 31 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 24 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 31 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 24 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Pure Standard Lean Comparison

`tools/compare-standard.js` now supports a `pure` mode for library exports in addition to the existing WASI command modes.  Pure mode compiles the selected entry with `compile`, invokes the exported function through `wasmtime --invoke`, and compares the printed result slots with a generated standard-Lean runner.  The runner evaluates a Lean call expression and prints a caller-provided `Array UInt64` slot expression, which makes flattened structure parameters and multi-slot structure or tagged results explicit in the test case rather than inferred by JavaScript.

The self-test now includes scalar results, bounded `Nat` results, structure results, flattened structure parameters, tagged results, flattened tagged parameters, and structural equality over products, structures, nonrecursive tagged values, and `Option` values.  It deliberately avoids examples whose purpose is to prove LeanExe's demand analysis skips a trapping expression, because the standard Lean runner may evaluate that expression before the value reaches the inspected field or tag.

Checks run:

- [x] `node tools/compare-standard.js --self-test` returned `checked 18 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 18 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Structural Equality Lowering

The extractor now lowers equality through a type-directed value comparison instead of routing every `BEq.beq`, `bne`, and `Eq` proposition through scalar extraction.  The supported equality fragment covers `Unit`, scalar values, products, structures, internal sums, `Option`, `Except`, and nonrecursive tagged values whose runtime fields also support equality.  The lowering compares fields in source order and compares tagged values by constructor tag before active payload fields, preserving short-circuit behavior for later fields and inactive constructor payloads.

At this checkpoint, array equality, `ByteArray` equality, and recursive-inductive equality remained unsupported because they needed explicit element iteration or heap traversal semantics.  The correctness cases covered product equality, structure equality, nested structures, proposition equality through `DecidableEq`, nonrecursive-inductive equality, `Option` equality over structures, and short-circuit cases whose skipped payloads would trap if evaluated.  The later heap-backed equality work superseded the array and byte-array limitation while retaining the recursive-inductive rejection.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 596 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 8 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Option and Except Do Notation

The extractor now recognizes `Option` and `Except ε` as supported monads for overloaded `Pure.pure`, `Bind.bind`, and `Functor.map`.  `Option` and `Except` `do` notation lowers to the same first-order tag and payload representation as the existing direct `Option.bind`, `Option.map`, `Except.bind`, and `Except.map` paths when callbacks are direct lambdas and payload types are concrete supported types.  `Functor.map` is now blocked from transparent unfolding, so Lean's class projection for the selected instance does not become a runtime function value.

The JSON examples now use the new source style where it improves the program shape.  `LeanExe.Examples.JsonAdd.parseInput` and `LeanExe.Examples.JsonCollatzLength.lengthInput?` use `Option` `do` notation, while `LeanExe.Examples.JsonGcd.transformAscii` uses `Except` `do` notation through a small `requireGcdInput` helper.  The standard Lean comparison self-test now includes the JSON add and JSON Collatz command entries.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 582 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 94 report classification cases`.
- [x] `lake build LeanExe.Examples.JsonAdd LeanExe.Examples.JsonCollatzLength LeanExe.Examples.JsonGcd lean-wasm`
- [x] `node test/json_double.js` returned `checked 48 json program cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 8 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 582 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 8 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Standard Lean Comparison Batch

The standard Lean comparison tool matched generated WASM for the main command-shaped examples that do not read LeanExe runtime counters.  The batch covered plain byte output, JSON field parsing and rendering, checked arithmetic failure encoded as JSON, Collatz JSON, GCD success and failure through `Except`, JSON tree construction, JSON tree search with stdin plus argv, and argv-only byte handling.

Checks run:

- [x] `LeanExe.Examples.JsonDouble.transform` under `stdin` with `{"n":21}`.
- [x] `LeanExe.Examples.JsonAdd.transform` under `stdin` with `{"a":19,"b":23}`.
- [x] `LeanExe.Examples.JsonAdd.transform` under `stdin` with `{"a":18446744073709551615,"b":1}`.
- [x] `LeanExe.Examples.JsonCollatzLength.transform` under `stdin` with `{"collatzLengthFor":41}`.
- [x] `LeanExe.Examples.JsonGcd.transform` under `stdin-except` with `[1,6,4,100,33,5,5,20]`.
- [x] `LeanExe.Examples.JsonGcd.transform` under `stdin-except` with `[]`.
- [x] `LeanExe.Examples.JsonTreeCommand.makeTree` under `stdin-except` with `[1,6,4,100,33,5,5,20]`.
- [x] `LeanExe.Examples.JsonTreeCommand.searchTree` under `stdin-argv-except` with a nested tree and search values `4` and `7`.
- [x] `LeanExe.Examples.ByteArrayPrograms.argvFirstLast` under `argv-except` with `alpha` and `omega`.
- [x] `LeanExe.Examples.Correctness.byteArrayAppendReturn` under `wasi`.

## 2026-05-15: Standard Lean Comparison Tool

`tools/compare-standard.js` compares a command-shaped entry against official Lean execution.  It generates a temporary Lean runner under `.lake/build/standard-compare`, runs that runner with `lake env lean --run`, compiles the same entry through the selected LeanExe WASI mode, runs the generated WASM with Wasmtime, and compares exit status, stdout, and stderr byte-for-byte.  The first supported modes are the byte-oriented command shapes: `wasi`, `stdin`, `stdin-except`, `argv-except`, and `stdin-argv-except`.

The tool deliberately treats standard Lean as the reference program, not as another hand-written expected-output fixture.  The runner writes standard Lean output to binary files with `IO.FS.writeBinFile`, which avoids text-encoding behavior in `IO.print`.  Programs that inspect `LeanExe.Runtime` counters are outside this comparison because standard Lean uses stub definitions while generated WASM reads runtime counters.

Checks run:

- [x] `node tools/compare-standard.js --self-test` returned `checked 6 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 6 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Growable Runtime Allocator

The runtime allocator now calls WASM `memory.grow` when neither the free list nor the current heap range can satisfy an allocation.  The generated memory still starts at 16 pages, and `reset()` still rewinds the heap to byte offset `4096`, but large library-mode allocations and compiled-code allocations can grow the module memory instead of trapping at the initial page boundary.  `test/refcount.js` now allocates a block as large as the initial memory, verifies that the memory grew, and writes the last byte of the returned range.

This changes the failure mode for large single requests.  Reference counting still matters because memory growth is bounded by the host and because long computations can allocate more live data than they need if dead generations are not released.  The JSON GC tree rewrite example now accepts `rounds <= 40`; a Wasmtime run for `{"depth":8,"rounds":40,"salt":17,"search":12345}` returned `nodeCount:255`, `height:8`, `allocsAfterInitial:575`, `freesAfterRounds:20440`, `releasesAfterFinal:20951`, and `freesAfterFinal:20951`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/refcount.js` returned `checked 5 refcount cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn --out .lake/build/refcount/byteArrayStringConstReturn.grow.wat`
- [x] `build/tools/wasmtime/current/wasmtime --invoke alloc .lake/build/refcount/byteArrayStringConstReturn.grow.wat 1048576` returned `4096`.
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonGcTreeRewrite --entry LeanExe.Examples.JsonGcTreeRewrite.transform --out .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":40,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":41,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm` returned `{"error":1}`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/core_correctness.js` returned `checked 574 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-15: JSON GC Tree Rewrite Benchmark

`LeanExe.Examples.JsonGcTreeRewrite` is a JSON-to-JSON WASI command that builds a balanced source-level tree, rewrites whole tree generations, releases the previous root after each rewrite, and releases the final root after computing metrics.  The input object contains `depth`, `rounds`, `salt`, and `search`.  The current accepted workload is `1 <= depth <= 8` and `rounds <= 40`, which exercises thousands of recursive-inductive frees.

The first implementation built a linear tree through a fuel-recursive structure accumulator.  That shape compiled but produced unusable runtime behavior once the tree passed roughly twenty nodes, because the accumulator carried a recursive heap root through every loop step.  The benchmark now builds the initial tree through direct balanced recursion by depth, then uses generation-level release boundaries.  A Wasmtime run for `{"depth":8,"rounds":20,"salt":17,"search":12345}` returned `nodeCount:255`, `height:8`, `allocsAfterInitial:575`, `freesAfterRounds:10220`, `releasesAfterFinal:10731`, and `freesAfterFinal:10731`.

Checks run:

- [x] `lake build LeanExe.Examples.JsonGcTreeRewrite`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonGcTreeRewrite --entry LeanExe.Examples.JsonGcTreeRewrite.transform --out .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":20,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":21,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm` returned `{"error":1}`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 4 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-15: Runtime Counters and Merge-Tree Release Demo

The runtime now maintains allocation, retain, release, and free counters in mutable WASM globals.  `LeanExe.Runtime.allocCount`, `retainCount`, `releaseCount`, and `freeCount` compile to reads of those globals, while `LeanExe.Runtime.release` compiles to an explicit release for monomorphic recursive-inductive heap roots.  Source-level release keeps a manual ownership precondition: the released root and any heap nodes it shares with live values must not be used after the call.

Recursive-inductive heap allocation now records a child-pointer mask in the object header.  The release runtime follows that mask and recursively releases child pointers before putting the current object on the free list.  Array objects have a mask slot in the runtime header, but the compiler still emits zero for array masks, so array child release remains future work.

`LeanExe.Examples.JsonMergeTreeCommand` reads two JSON integer arrays, builds one source-level binary-search tree for each, constructs a third merged tree by copying values from the first two trees, and then releases the first two roots.  The command emits the merged tree plus GC counters, and its companion search command reads the intermediate object and searches the final tree.  A Wasmtime run for `[[1,6,4,100],[33,5,5,20]]` reported `allocs:145`, `freesBefore:0`, `freesAfterFirst:9`, `freesAfterSecond:18`, and `releasesAfterSecond:18` before search.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.JsonMergeTreeCommand`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module LeanExe.Examples.JsonMergeTreeCommand --entry LeanExe.Examples.JsonMergeTreeCommand.makeMergedTree --out .lake/build/wasi-programs/makeMergedTree.stdin-except.wasi.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except --max-input-bytes 8192 --max-args 8 --max-argv-bytes 256 --module LeanExe.Examples.JsonMergeTreeCommand --entry LeanExe.Examples.JsonMergeTreeCommand.searchMergedTree --out .lake/build/wasi-programs/searchMergedTree.stdin-argv-except.wasi.wasm`
- [x] `printf '[[1,6,4,100],[33,5,5,20]]' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/makeMergedTree.stdin-except.wasi.wasm`
- [x] `printf '[[1,6,4,100],[33,5,5,20]]' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/makeMergedTree.stdin-except.wasi.wasm | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/searchMergedTree.stdin-argv-except.wasi.wasm 4` returned `{"found":true,"allocs":849,"releases":0,"frees":0}`.
- [x] `node test/wasi_program.js` returned `checked 20 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 4 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 20 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: JSON Tree Example Cleanup

`LeanExe.Examples.JsonTreeCommand` now renders the intermediate tree through the JSON AST renderer instead of assembling byte-level object fragments by hand.  The example keeps the attached-field fold in `decodeTree`, because that spelling exposes the field-membership proof Lean needs for structural recursion and matches the well-founded-recursion shape the compiler already supports.  A getter-based recursive decoder is valid Lean, but Lean lowers it through a generated well-founded shape outside the current extractor.

`LeanExe.Ascii.Json.Value` now provides reusable object helpers for nonrecursive AST consumers: `countField`, `getUniqueField?`, `nameInArray`, and `allFieldNamesIn`.  The helper theorem for unique field lookup records that a returned field value is structurally smaller than the containing field array, which is useful for future recursive decoders once the extractor accepts the corresponding generated shape.

Checks run:

- [x] `lake build LeanExe.Examples.JsonTreeCommand`
- [x] `node test/wasi_program.js`

## 2026-05-14: AST JSON Parser and Tree Pipeline

`LeanExe.Ascii.Json.Value` adds an ASCII-only JSON AST with `null`, booleans, unsigned `UInt64` numbers, restricted unescaped strings, arrays, and objects.  The parser is a single bounded recursive dispatcher over a request type, so recursive descent uses one accepted Nat-recursive helper with an explicit parse mode and tagged parse result.  The tree command now parses both the input array and the intermediate tree JSON through that AST, and it emits the tree through JSON writer helpers instead of embedding punctuation fragments in the example.

`JsonTreeCommand.buildTree` uses `Array.foldl` over parsed JSON array elements.  It no longer carries an explicit fuel counter for that scan, because the compiler supports `Array.foldl` with a supported structure accumulator and direct-lambda folder.  `JsonTreeCommand.searchTree` now decodes the parsed JSON AST into the source-level `Tree` type before searching.  The search is ordinary structural recursion over `Tree`, so the example no longer needs a bounded search through object-field lookup.

The extractor now represents materialized internal values as `LocalLet` blocks when a fold body or source `let` produces a multi-slot structure.  Fold IR nodes carry those blocks and the WASM emitter runs them once per iteration before assigning the next accumulator slots.  The local-let liveness pass removes definitions that the demanded projection or returned value does not use, preserving Lean's lazy behavior for unused fields while still avoiding repeated recursive calls in structured fold bodies.

The compiler now accepts expression-position calls to the generated Nat-recursive handle by emitting an ordinary WASM call with decremented fuel.  Tail-position calls still lower to the existing loop form, so parser loops keep the efficient path when the source branch is a plain continuation.  Fuel-recursive steps that match a recursive inductive now fall back to exit-expression lowering, which allows bounded search helpers to inspect recursive AST values without treating the match as loop control.

Checks run:

- [x] `lake build LeanExe.Ascii.Json.Value`
- [x] `lake build LeanExe.Examples.JsonTreeCommand`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.makeTree --out build/make-tree.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except --max-input-bytes 8192 --max-args 8 --max-argv-bytes 256 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.searchTree --out build/search-tree.wasm`
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/current/wasmtime run build/make-tree.wasm | build/tools/wasmtime/current/wasmtime run build/search-tree.wasm 4` returned `{"found":true}`.
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/current/wasmtime run build/make-tree.wasm | build/tools/wasmtime/current/wasmtime run build/search-tree.wasm 7` returned `{"found":false}`.
- [x] `node test/wasi_program.js` returned `checked 19 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 19 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: JSON Array GCD Command

`LeanExe.Ascii.Json.parseArrayRanges` scans a JSON array and returns raw element ranges.  It is a JSON-level scanner: callers decide how to interpret each element.  `LeanExe.Examples.JsonGcd.transform` uses that scanner to read a nonempty array of decimal `UInt64` values from stdin under `compile-wasi-stdin-except`, computes their GCD, and writes `{"gcd":N}` to stdout.

Checks run:

- [x] `lake build LeanExe.Examples.JsonGcd`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonGcd --entry LeanExe.Examples.JsonGcd.transform --out .lake/build/json-gcd.wasm`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime run .lake/build/json-gcd.wasm < /tmp/leanexe-json-gcd-input.json`
- [x] `node test/wasi_program.js`
- [x] `node test/run_all.js`

## 2026-05-14: JSON Example Cleanup

`LeanExe.Examples.JsonDouble` and `LeanExe.Examples.JsonAdd` use `Ascii.Json.getUInt64Field` for input and `Ascii.Json.object1UInt64` for output.  Both examples share the library field scanner and object generator.  Their behavior matches the documented limited JSON API: requested fields are order-independent, unknown supported values may be skipped, and malformed input or arithmetic overflow returns `{"error":1}`.

Checks run:

- [x] `lake build LeanExe.Examples.JsonDouble LeanExe.Examples.JsonAdd LeanExe.Examples.JsonCollatzLength LeanExe.Examples.JsonTools`
- [x] `node test/json_double.js`
- [x] `node test/run_all.js`

## 2026-05-06

The repository started with `plan.md` only.  The first implementation step creates a Lake package pinned to Lean 4.29.1, because elan reports that toolchain as installed and active.  No third-party Lean, JavaScript, or Wasm dependencies were added.

The initial executable target is narrow by design.  It supports the checked Lean declaration `LeanExe.Examples.AsciiDigits.validate : ByteArray -> Bool`, lowers it to a byte-range validator, and emits a standalone Wasm module with `memory`, `alloc`, `reset`, and `validate` exports.  Wasm compilation from the generic report, monomorphization, and typeclass specialization remain unimplemented.

Authoritative references used:

| Topic | Reference |
| ----- | --------- |
| Installed Lean toolchain | `elan show` |
| Lake project syntax | `lake init LeanExe exe.lean` template in `/tmp/lake-template-check` |
| Lean `ByteArray` API | Local Lean `#check` commands against Lean 4.29.1 |
| WebAssembly binary encoding | WebAssembly Core Specification binary format |
| Wasmtime release artifacts | https://github.com/bytecodealliance/wasmtime/releases |

Current plan:

- [x] Create a Lake package and project root.
- [x] Add a byte-array validator with a Lean soundness theorem.
- [x] Add a small core IR and evaluation semantics.
- [x] Add proof-erasure and lowering correctness lemmas for the first boundary.
- [x] Add a Wasm emitter for the lowered validator.
- [x] Add a Node host runner and fuzz differential harness.
- [x] Build the project with Lake: `lake build`.
- [x] Emit the report and Wasm module: `.lake/build/bin/lean-wasm emit --out build/validate.wasm`, `.lake/build/bin/lean-wasm wat --out build/validate.wat`, and `.lake/build/bin/lean-wasm report --out build/extraction-report.txt`.
- [x] Run Lean/Wasm differential tests: `node test/fuzz_validate.js build/validate.wasm 200`.

## 2026-05-06: Checked-Environment Report

The next implementation step adds `spec.md` and a checked-environment report path.  The report uses Lean’s `importModules` API, `Environment.find?`, `ConstantInfo`, and `Expr.getUsedConstants` from the installed Lean 4.29.1 toolchain.  It imports a compiled module, finds an entry constant, expands project-local dependencies by root namespace, and records external dependencies as a classified frontier.

The report does not claim generic compilation.  It classifies declarations so the next compiler step has concrete blockers rather than an unstructured failure.  The current classifier detects unsupported effects, higher-order argument types, polymorphic declarations, typeclass instance dependencies, external library operations, `unsafe`, `partial`, opaque constants, axioms, quotients, inductives, constructors, and recursors.

Commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm report --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validate --out build/env-report.txt`
- [x] `.lake/build/bin/lean-wasm report --module Main --entry main`

## 2026-05-06: Collatz Demo

`LeanExe.Examples.Collatz.steps : UInt64 -> UInt64` computes Collatz steps with a `10000`-step fuel bound.  The bound avoids `partial` recursion and avoids assuming the global Collatz conjecture.  The first Collatz Wasm emitter used a Collatz-specific byte emitter.  That path was removed.  The current path uses `lean-wasm compile --module <module> --entry <name> --out <path>`, which loads checked declarations, extracts the supported first `UInt64` fragment into `LeanExe.IR.Core`, and emits Wasm from that IR.

Planned checks:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm collatz-eval --input 27`
- [x] Run `build/collatz.wasm` with Wasmtime 36.0.9 from `/tmp`: `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_steps build/collatz.wasm 27`.

Limitation at that checkpoint: the generic compiler fragment supported only monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, primitive arithmetic, direct calls, `if`, boolean equality and disjunction, and tail recursion over a decreasing `Nat` fuel argument.  It did not lower arbitrary Lean expressions, data structures, pattern matching over user inductives, arrays, byte arrays, typeclasses beyond the primitive patterns it recognized, or IO.  `compile-wat` printed WAT from the same IR used by binary emission.  The verification pass compared Lean and Wasmtime for `27`, `989345275647`, `bench 27 10`, and `bench 989345275647 3`.

## 2026-05-06: Collatz Timing

OEIS A284668 lists `989345275647` as the smallest number below `10^12` with the largest total stopping time in that range.  A local arbitrary-precision check gives `1348` steps and a maximum trajectory value of `1219624271099764`, which fits in `UInt64`.

The timing comparison used `collatz_bench(n, iters)`, which repeats the computation inside the Lean executable or inside the Wasm module and returns the sum of all step counts.  This avoided measuring one process start per Collatz sequence.  These timing notes predate the generic compiler path and should be rerun before serving as current benchmark evidence.

Superseded commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm collatz-emit --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 27 --iters 10000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 27 10000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 63728127 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 63728127 1000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 989345275647 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 989345275647 1000000`

## 2026-05-06: Generic UInt64 Compiler Fragment

`LeanExe.IR.Core` is now the generic executable IR for the first compiler fragment.  `LeanExe.Extract.Core` loads checked declarations from a Lean environment, collects supported project-local function dependencies, extracts the accepted `UInt64` and bounded-`Nat` fragment, and emits through `LeanExe.Wasm.Binary.CoreWasm`.  Collatz now compiles through `lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`; there is no `LeanExe.Extract.Collatz` compiler path.

At this checkpoint, the first fragment supported monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, numeric literals, primitive `UInt64` arithmetic, `if`, boolean equality, boolean conjunction and disjunction, direct calls, and tail recursion over a decreasing `Nat` fuel argument.  Unsupported code failed during extraction with a reason.  Source-to-IR correctness remained unproved.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.bench --out build/collatz-bench.wasm`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke steps build/collatz.wasm 27`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke steps build/collatz.wasm 989345275647`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke bench build/collatz-bench.wasm 27 10`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke bench build/collatz-bench.wasm 989345275647 3`
- [x] `lake build LeanExe.Examples.Arithmetic`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Arithmetic --entry LeanExe.Examples.Arithmetic.affine --out build/affine.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Arithmetic --entry LeanExe.Examples.Arithmetic.choose --out build/choose.wasm`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke affine build/affine.wasm 5 11`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke choose build/choose.wasm 0 41`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke choose build/choose.wasm 8 41`
- [x] `node test/fuzz_validate.js build/validate.wasm 200`

## 2026-05-06: Naive Integer Map

`LeanExe.Examples.IntMap` is a simple open-addressed table from `UInt64` keys to `UInt64` values.  It uses 256 slots, stores each slot as adjacent key and value cells in an `Array UInt64`, reserves key `0` as empty, inserts keys `1` through `100`, maps key `k` to `k * 10 + 7`, and exports `query` and `checksum`.  `checksum` sums all 100 mapped values and returns `51200`.

The example required generic array support in the checked-declaration compiler.  At this checkpoint, the IR had `Array UInt64` pointer values, zero-filled allocation, indexed loads, and indexed stores.  The extractor recognized `Array.replicate n 0`, `Array.get!Internal`, `Array.set!`, boolean-valued helper functions represented as `0` or `1`, and zero-argument project declarations used as constants.  It rejected nonzero `Array.replicate` fills, because the Wasm lowering did not initialize arbitrary values.

That initial array lowering mutated Wasm memory in place and assumed linear use of arrays across updates.  That matched the integer-map example, but it did not implement Lean array alias semantics.  The later copy-on-write array section supersedes this lowering.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.query --out .lake/build/intmap-query.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.query --out .lake/build/intmap-query.wat`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.checksum --out .lake/build/intmap-checksum.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 1` returned `17`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 100` returned `1007`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 101` returned `0`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke checksum .lake/build/intmap-checksum.wasm` returned `51200`.
- [x] `lake env lean --stdin` with `#eval LeanExe.Examples.IntMap.query 1`, `#eval LeanExe.Examples.IntMap.query 100`, `#eval LeanExe.Examples.IntMap.query 101`, and `#eval LeanExe.Examples.IntMap.checksum` returned `17`, `1007`, `0`, and `51200`.

## 2026-05-06: Next Prime

`LeanExe.Examples.Prime.next : UInt64 -> UInt64` returns the first prime greater than the input within a fixed search fuel of `100000` candidate values.  It uses a naive divisor scan from `2` to `n - 1`, represented as decreasing `Nat`-fuel recursion, and returns `0` if the candidate search fuel is exhausted.  This example exercises the scalar compiler path without adding new primitives.

Checks run:

- [x] `lake build LeanExe.Examples.Prime`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Prime --entry LeanExe.Examples.Prime.next --out .lake/build/prime-next.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Prime --entry LeanExe.Examples.Prime.next --out .lake/build/prime-next.wat`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 0` returned `2`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 2` returned `3`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 14` returned `17`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 1000` returned `1009`.
- [x] `lake env lean --stdin` with the same four `#eval LeanExe.Examples.Prime.next` calls returned `2`, `3`, `17`, and `1009`.

## 2026-05-06: Correct Array UInt64 Semantics

The CoreWasm array layout now stores `Array UInt64` values as pointers to a length header followed by eight-byte cells.  `Array.replicate n 0` writes the length and allocates zero-filled cells.  `Array.get!Internal` and `GetElem?.getElem!` check the index before loading; an out-of-bounds index emits a Wasm trap, matching ordinary Lean execution of `a[i]!`.  `Array.set!` evaluates its arguments, checks the index, allocates a fresh array, copies all cells, updates one cell, and returns the new pointer.  Old aliases keep pointing at the old array.

`LeanExe.Examples.ArraySemantics.aliasCheck` captures the aliasing case that the old in-place lowering got wrong.  The program builds a base array with element `0` equal to `11`, computes `(a.set! 0 22)[0]! * 100 + a[0]!`, and returns `2211`.  The old in-place lowering would have returned `2222`.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.aliasCheck --out .lake/build/array-alias.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.oobGet --out .lake/build/array-oob-get.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.oobSet --out .lake/build/array-oob-set.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke aliasCheck .lake/build/array-alias.wasm` returned `2211`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke oobGet .lake/build/array-oob-get.wasm` trapped with `wasm unreachable`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke oobSet .lake/build/array-oob-set.wasm` trapped with `wasm unreachable`.
- [x] `lake env lean --stdin` with `#eval LeanExe.Examples.ArraySemantics.aliasCheck` returned `2211`.
- [x] The integer-map regression still returned `17`, `1007`, `0`, and `51200` for `query 1`, `query 100`, `query 101`, and `checksum`.

## 2026-05-06: Local Let Bindings

The generic extractor now lowers Lean `.letE` expressions into `LeanExe.IR.Expr.letE` with an explicit local slot.  The slot allocator threads through nested expressions, branches, conditions, call arguments, and the supported `Nat.brecOn` tail-recursion shape.  Recursive update temporaries now start after locals required by extracted loop conditions and recursive arguments, preventing collisions between let-bound locals and loop-update staging slots.

The CoreWasm emitter lowers an IR let by evaluating the bound value, assigning it to the chosen Wasm local, and emitting the body.  At that checkpoint, the implementation accepted let-bound `Bool`, `UInt64`, bounded `Nat`, and `Array UInt64` values.  Product lets were added later.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Let`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.aliasLet --out .lake/build/let-alias.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.singleArrayUse --out .lake/build/let-single-array.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.boolLet --out .lake/build/let-bool.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.letCondition --out .lake/build/let-condition.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.recArgLetDemo --out .lake/build/let-rec-arg.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.branchArray --out .lake/build/let-branch-array.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.bumpDemo --out .lake/build/let-bump-demo.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke aliasLet .lake/build/let-alias.wasm` returned `2211`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke singleArrayUse .lake/build/let-single-array.wasm` returned `14`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolLet .lake/build/let-bool.wasm 3` returned `44`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolLet .lake/build/let-bool.wasm 2` returned `55`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke letCondition .lake/build/let-condition.wasm 3` returned `1`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke letCondition .lake/build/let-condition.wasm 2` returned `0`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke recArgLetDemo .lake/build/let-rec-arg.wasm` returned `10`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke branchArray .lake/build/let-branch-array.wasm 0` returned `5`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke branchArray .lake/build/let-branch-array.wasm 1` returned `9`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bumpDemo .lake/build/let-bump-demo.wasm` returned `2`.
- [x] Lean evaluation for `aliasLet`, `singleArrayUse`, `boolLet 3`, `boolLet 2`, `letCondition 3`, `letCondition 2`, `recArgLetDemo`, `branchArray 0`, `branchArray 1`, and `bumpDemo` returned `2211`, `14`, `44`, `55`, `1`, `0`, `10`, `5`, `9`, and `2`.
- [x] At that checkpoint, `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.unsupportedLetPair --out .lake/build/let-unsupported-pair.wasm` failed with `unsupported let-bound type: Prod.{0, 0} UInt64 UInt64`.

## 2026-05-06: Core Correctness Corpus

`LeanExe.Examples.Correctness` collects small checked Lean programs that stress semantic edges in the generic compiler fragment.  At that checkpoint, the accepted cases covered boolean short-circuiting with skipped traps, `UInt64` division and remainder at zero divisors, wraparound arithmetic, nested lexical shadowing, lets in call arguments, array update and read ordering, and lets inside recursive arguments.  The rejected cases covered product lets, nonzero array replication, higher-order arguments, and `IO`.

The corpus found three concrete issues.  CoreWasm condition lowering used Wasm `i32.and` and `i32.or`, which evaluated both operands and therefore trapped for `true || rhs` and `false && rhs` when `rhs` contained an out-of-bounds array access.  CoreWasm `UInt64` division and remainder used Wasm `i64.div_u` and `i64.rem_u` directly, but Lean returns `0` for `x / 0` and `x` for `x % 0`.  The signed LEB128 encoder for `i64.const` emitted invalid Wasm for `UInt64` constants above `Int64.max`; those constants now lower through the signed two’s-complement representation of the same 64-bit pattern.

The corpus also exposed a limitation in the first `Nat.brecOn` tail-recursion extractor.  The old lowering assumed that the loop result was the last carried parameter.  The extractor now parses the generated matcher, extracts the base arm, extracts an optional early-exit value from the successor arm, and emits a result expression that distinguishes fuel exhaustion from early exit.  The successor arm still must either tail-call the recursive handle or use `if cond then exitValue else recursiveCall`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] Lean evaluation for `shortOrSkipsTrap`, `shortAndSkipsTrap`, `divByZero`, `modByZero`, `overflow`, `underflow`, `nestedShadow 3`, `callArgLets 7`, `arrayUpdateRead`, `recLetDemo`, and `recExitDemo` returned `1`, `0`, `0`, `5`, `0`, `18446744073709551615`, `64`, `809`, `110`, `518`, and `314`.
- [x] `node test/core_correctness.js` returned `checked 11 accepted and 4 rejected cases`.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Wasmtime regressions returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

## 2026-05-06: Internal Product Values

The extractor now represents products as structured extractor values rather than Wasm values.  Product construction, `.1`, `.2`, product-valued local lets, product-valued `if` expressions, nested products, products containing `Array UInt64` pointers, and projections inside recursive-call arguments compile when every field belongs to the first fragment.  Product-valued entry parameters and product-valued entry results remain rejected, because the CoreWasm ABI still exports scalar `i64` values and array pointers only.

Product projection follows Lean’s lazy projection behavior.  `(bad, value).2` and `let pair := (bad, value); pair.2` do not evaluate `bad`, so the extractor keeps products as field expressions and selects the demanded field.  The same work fixed unused scalar lets: `let x := bad; value` no longer forces `bad` when `x` is not referenced by the body.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] Lean evaluation for `productLet`, `nestedProduct`, `productSkipsUnusedField`, `productBranch 0`, `productBranch 1`, `productArrayAlias`, `recProductDemo`, and `unusedScalarLetSkipsTrap` returned `12`, `203`, `7`, `12`, `34`, `2211`, `10`, and `1`.
- [x] `node test/core_correctness.js` returned `checked 19 accepted and 5 rejected cases`.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Node WebAssembly smoke regressions returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

## 2026-05-06: Lazy Bindings, Option Values, and Strict Calls

The next correctness pass found a mismatch between Lean evaluation and the eager scalar-let lowering.  Lean returns `7` for `let x := bad; (x, 7).2`, because the projection does not demand the first product field.  The extractor now represents let-bound values as thunks over the checked expression and its de Bruijn environment, forcing the thunk only when the body demands it.

The same issue applies to nonrecursive helper calls.  Lean returns `1` for `ignore bad` when the helper ignores its argument, while Wasm function calls evaluate arguments before entering the callee.  The extractor now inlines nonrecursive project-local helper calls with lazy argument thunks; recursive helpers still compile as Wasm functions when the supported `Nat.brecOn` loop extraction requires that representation.

The extractor now computes demand summaries for project-local helper calls.  Each summary records parameters that may be demanded and parameters that must be demanded when the helper result is demanded.  Strict Wasm calls are rejected when an argument may trap and the callee does not must-demand the corresponding parameter.  `LeanExe.Examples.Correctness.rejectRecursiveIgnoredTrapArg` captures the direct case: Lean evaluates the program to `7`, while the old Wasm lowering trapped before the helper could take its fuel-zero base branch.  `rejectRecursiveIgnoredHiddenTrapArg` captures the indirect case, where the trap is hidden behind a zero-argument project-local declaration.  Recursive summaries are conservative: the fuel parameter is must-demanded, carried parameters are may-demanded, and a later pass should either inline supported loop calls at the call site or compute more precise carried-parameter demand.

`Option` values are now extractor-level tagged values.  `Option.none`, `Option.some`, local `Option` lets, `if` expressions returning `Option`, and matches over `Option UInt64` compile when the final entry result remains a scalar first-fragment value.  `Option` entry parameters and entry results remain rejected because the current Wasm ABI exposes only scalar `i64` values and array pointers.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 29 accepted and 9 rejected cases`.
- [x] Lean evaluation for `letUsedOnlyInUnusedProductField`, `ignoredCallArgSkipsTrap`, `callArgUsedOnlyInUnusedProductField`, `optionSomeMatch`, `optionNoneMatchSkipsSomeArm`, `optionSomeMatchSkipsUnusedPayload`, `optionLet`, `optionBranch 0`, and `optionBranch 1` returned `7`, `1`, `7`, `8`, `5`, `9`, `18`, `11`, and `34`.
- [x] Lean evaluation for `recursiveDemandedFuelGet`, `rejectRecursiveIgnoredTrapArg`, and `rejectRecursiveIgnoredHiddenTrapArg` returned `7`, `7`, and `7`; compilation accepts the demanded-fuel case and rejects the ignored-argument cases.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Wasmtime 44.0.0 from `build/tools/wasmtime/current/wasmtime` returned `11` and `34` for `optionBranch 0` and `optionBranch 1`.
- [x] Wasmtime regressions returned `111` for `Collatz.steps 27`, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `2211` for array aliasing.

## 2026-05-06: Generic Read-Only ByteArray Input

The generic compiler now accepts a `ByteArray` parameter as a structured extractor value backed by two Wasm ABI slots: pointer and length.  `ByteArray.size` reads the length slot, and `ByteArray.get!` lowers to a bounds check followed by `i32.load8_u` and zero extension to the scalar `i64` representation.  Function calls and the supported `Nat.brecOn` loop shape flatten `ByteArray` values when crossing a strict Wasm call boundary, while Lean source functions still see one `ByteArray` parameter.

`LeanExe.Examples.AsciiDigits.validateGeneric : ByteArray -> Bool` is the first byte-buffer program compiled through `lean-wasm compile`.  It keeps the original proof-oriented `validate` declaration unchanged and uses a fuel-bounded loop over the input length plus one, so the empty input returns `true` and the terminal length check does not read past the end of the buffer.  The generic validator is still read-only: the host writes bytes into exported memory and calls the entry function as `validateGeneric(ptr, len)`.

Wasmtime was no longer present under `/tmp`, so this pass downloaded the official Wasmtime 36.0.9 `aarch64-linux` release into `.lake/build/tools`.  That release is marked latest on the upstream GitHub releases page as of 2026-05-06.  The Wasmtime check uses a generated WAST file with active data segments because the generic module exports memory but does not yet export `alloc` or a host helper for writing byte inputs through the CLI.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `.lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --version` returned `wasmtime 36.0.9 (c59270b18 2026-05-05)`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted generated assertions for empty input, all-digit input, invalid input, and a valid prefix.

## 2026-05-06: Generic Comparison Primitives

The generic IR now has unsigned `<` and `<=` conditions.  The extractor recognizes Lean conditions elaborated as `LT.lt` and `LE.le`, including conditions over bounded `Nat` and `UInt64` values, and CoreWasm lowers them to `i64.lt_u` and `i64.le_u`.  This keeps the current fixed-width representation explicit: accepted runtime `Nat` comparisons are comparisons over the bounded `i64` values already admitted into the fragment, not arbitrary-precision `Nat` execution.

`LeanExe.Examples.AsciiDigits.isAsciiDigitNat` now uses the source-level range check `48 <= n` and `n <= 57` instead of ten equality tests.  `LeanExe.Examples.Correctness` adds separate `Nat` and `UInt64` comparison cases for values below, at, and above the branch boundary.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 35 accepted and 9 rejected cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted generated assertions for empty input, all-digit input, invalid input, and a valid prefix.

## 2026-05-06: Generic Array Size

The generic IR now has `Array.size` as a scalar expression.  CoreWasm lowers it to an `i64.load` from the array header, the same header already used by bounds checks and copy-on-write updates.  This lets source programs inspect array lengths without adding a new layout rule.

`LeanExe.Examples.Correctness.arraySizeAfterSet` checks that `Array.set!` preserves the length header while returning a fresh array pointer.  The function returns `Nat`, which remains represented as an `i64` in the bounded fragment.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 36 accepted and 9 rejected cases`.

## 2026-05-06: Generic Array Push

The generic compiler now lowers `Array.push` for `Array UInt64`.  CoreWasm evaluates the source array and pushed value, loads the old length, allocates a new array with length `oldLen + 1`, copies existing cells, writes the pushed value at the old length, and returns the new pointer.  This matches the conservative copy-on-write discipline already used by `Array.set!`, so old aliases keep the old length and old cells.

`LeanExe.Examples.Correctness.arrayPushRead` checks the pushed length, old-array length, preserved first cell, and new last cell.  The direct Wasmtime check exercises the emitted binary for that example rather than only Node’s WebAssembly runtime.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 37 accepted and 9 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayPushRead .lake/build/core-correctness/arrayPushRead.wasm` returned `507`.

## 2026-05-06: Generic Allocator Exports

Generic CoreWasm modules now export `alloc(len : i64) -> i64` and `reset()`.  The heap global starts at byte offset `4096`, matching the original validator module, and every generic array allocation uses the same heap global.  A host that needs to pass a `ByteArray` can now call `reset`, call `alloc`, write bytes at the returned pointer, and pass `(ptr, len)` to the entry function without guessing a memory address that might overlap later compiled allocations.

The generic function indices remain stable because the runtime functions are appended after user functions.  User calls still refer to the same indices, and the runtime exports use indices `funcs.size` and `funcs.size + 1`.  The validator fuzz harness now uses the generic allocator when `validateGeneric`, `alloc`, and `reset` are present, while retaining support for the older hand-written validator ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 37 accepted and 9 rejected cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke alloc .lake/build/ascii-generic.wasm 4` returned `4096`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted allocator and validator assertions.

## 2026-05-06: Nonzero Array Replication

`Array.replicate` now supports nonzero `UInt64` fill values.  CoreWasm still uses the zero-allocation path for literal zero fills, but nonzero fills evaluate the length and value, allocate the array header and cells, and run a fill loop that writes the value into each cell.  The value is evaluated once before the fill loop, matching the source-level call argument.

`LeanExe.Examples.Correctness.nonzeroReplicateRead` checks the new path by reading two initialized cells and checking the resulting size.  The previous rejection case for nonzero replication was removed from the correctness harness because the feature now compiles.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 38 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke nonzeroReplicateRead .lake/build/core-correctness/nonzeroReplicateRead.wasm` returned `77`.

## 2026-05-06: Generic Array Pop

The generic compiler now lowers `Array.pop` for `Array UInt64`.  Empty arrays return the original pointer, matching Lean’s empty-pop behavior.  Nonempty arrays allocate a fresh array with length `oldLen - 1`, copy the retained prefix, and return the new pointer, preserving the copy-on-write rule used by `set!` and `push`.

`LeanExe.Examples.Correctness.arrayPopRead` checks pop after push, the old array length, the popped array length, empty-pop behavior, and retained cells.  The Wasmtime check runs the emitted binary for that example.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 39 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayPopRead .lake/build/core-correctness/arrayPopRead.wasm` returned `44`.

## 2026-05-06: UInt64 Bitwise Or and Xor

The scalar IR now supports `UInt64.lor` and `UInt64.xor`, complementing the existing `UInt64.land` lowering.  CoreWasm emits `i64.or` and `i64.xor`; these operations preserve the current fixed-width `UInt64` representation without adding new ABI rules.

`LeanExe.Examples.Correctness.bitwiseOrXor` checks the new operations together with `land`, and Wasmtime runs the emitted binary for that case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 40 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bitwiseOrXor .lake/build/core-correctness/bitwiseOrXor.wasm` returned `6`.

## 2026-05-06: UInt64 Shifts

The scalar IR now supports `UInt64.shiftLeft` and `UInt64.shiftRight`.  Local Lean checks showed that Lean masks the shift count modulo 64 for `UInt64`, matching Wasm `i64.shl` and `i64.shr_u`; for example, shifting by `65` behaves like shifting by `1`.

`LeanExe.Examples.Correctness.shiftMasking` checks both left and right shifts with a count of `65`, and Wasmtime runs the emitted binary for that case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 41 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke shiftMasking .lake/build/core-correctness/shiftMasking.wasm` returned `42`.

## 2026-05-06: Greater-Than Comparisons

The extractor now recognizes Lean conditions elaborated as `GT.gt` and `GE.ge`.  They lower by reversing the operands of the existing unsigned `<` and `<=` IR conditions, so no new Wasm condition form was needed.

`LeanExe.Examples.Correctness.greaterComparisons` checks `>` and `>=` across the below, boundary, and above cases.  Wasmtime runs the emitted binary for the above case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 44 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke greaterComparisons .lake/build/core-correctness/greaterComparisons.wasm 6` returned `30`.

## 2026-05-06: Reserved Runtime Export Names

Generic modules now reject entry points whose short export name would collide with runtime exports.  The reserved names are `memory`, `alloc`, and `reset`.  Without this check, a source function named `alloc` could compile to a module with duplicate exports after the generic allocator was added.

`LeanExe.Examples.Correctness.alloc` is a valid scalar Lean definition, but compiling it as an entry now fails with `entry export name is reserved by the runtime ABI: alloc`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 44 accepted and 9 rejected cases`.

## 2026-05-06: ByteArray Input with Later Allocation

`LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray` exercises a mixed ByteArray-and-array program.  The host passes a `ByteArray` through the generic `(ptr, len)` ABI, and the compiled function then allocates an `Array UInt64` before reading the input byte.  This catches heap-overlap regressions in the generic allocator: input allocated by the host must remain valid after compiled code allocates.

`test/bytearray_alloc.js` builds the example module, compiles it through `lean-wasm compile`, allocates host input through the module’s exported allocator, writes the bytes into memory, and calls the compiled entry.  The Wasmtime WAST check covers the same scenario with an active data segment at the allocator’s first returned pointer.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray --out .lake/build/bytearray-first-plus-array.wasm`
- [x] `node test/bytearray_alloc.js` returned `checked 3 bytearray allocation cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray --out .lake/build/bytearray-first-plus-array.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/bytearray-first-plus-array.wast` accepted the allocator-plus-entry assertion.

## 2026-05-06: Nat Subtraction Semantics

The extractor previously lowered every `HSub.hSub` application to wrapping `i64.sub`.  That was correct for `UInt64`, but wrong for `Nat`: Lean’s `Nat` subtraction saturates at zero.  The extractor now inspects the primitive result type and emits a dedicated bounded-`Nat` subtraction operation for `Nat` results.  CoreWasm evaluates both operands once, returns `0` when `left < right`, and otherwise emits `left - right`.

`LeanExe.Examples.Correctness.natSubSaturates` checks the underflow case, and `natSubNormal` checks ordinary subtraction.  `UInt64` subtraction still uses wrapping subtraction, so the existing `underflow` test continues to return `18446744073709551615`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 46 accepted and 9 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natSubSaturates .lake/build/core-correctness/natSubSaturates.wasm` returned `0`.

## 2026-05-06: Bounded Nat Literal Rejection

Runtime `Nat` literals now receive an explicit bound check during extraction.  Literals below `2^64` continue to lower to the scalar `i64` representation; larger literals are rejected with `Nat literal exceeds bounded runtime representation`.  This avoids silently compiling an arbitrary-precision Lean `Nat` literal to its low 64 bits.

`LeanExe.Examples.Correctness.rejectHugeNatLiteral` covers the first out-of-range value, `18446744073709551616`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 46 accepted and 10 rejected cases`.

## 2026-05-06: Checked Nat Addition and Multiplication

The extractor now emits distinct IR operations for `Nat` addition and multiplication instead of reusing wrapping `UInt64` operations.  `Nat` addition evaluates both operands once, computes the `i64` sum, and traps if the unsigned result wrapped below the left operand.  `Nat` multiplication traps when `left > UInt64.max / right`, with a separate zero case.  These traps mark values outside the current bounded `Nat` subset rather than returning a truncated result.

The correctness harness now has a third category for programs that compile but must trap at runtime.  `natAddOverflow` and `natMulOverflow` cover the first overflowing values.  Normal `Nat` addition and multiplication still compile and return their expected bounded results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 48 accepted, 10 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natAddOverflow .lake/build/core-correctness/natAddOverflow.wasm` trapped with `wasm unreachable`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natMulOverflow .lake/build/core-correctness/natMulOverflow.wasm` trapped with `wasm unreachable`.

## 2026-05-06: UInt64.ofNat

The extractor now recognizes `UInt64.ofNat`.  For a literal argument, it lowers directly to a `UInt64` constant, preserving Lean’s modulo-`2^64` behavior for large literals.  For a runtime `Nat` expression, it lowers the bounded scalar value directly; values outside the bounded `Nat` representation cannot arise without a prior trap.

`LeanExe.Examples.Correctness.uint64OfNatValue` checks a runtime bounded conversion, and `uint64OfHugeNat` checks that a literal equal to `2^64` converts to `0` rather than receiving the bounded-`Nat` literal rejection.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 50 accepted, 10 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint64OfHugeNat .lake/build/core-correctness/uint64OfHugeNat.wasm` returned `0`.

## 2026-05-06: ByteArray Result Rejection

The function type checker now distinguishes parameter ABI support from result ABI support.  A `ByteArray` parameter is allowed and flattens to `(ptr, len)`, but a `ByteArray` result is rejected because generic CoreWasm functions still return one `i64`.  This moves byte-array result rejection to the function type boundary instead of letting extraction fail later when a structured value is used as a scalar.

`LeanExe.Examples.Correctness.rejectByteArrayReturn` covers the case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 50 accepted, 11 rejected, and 2 trapped cases`.

## 2026-05-06: Internal UInt8 Values

`ByteArray.get!` returns `UInt8`, so byte-oriented programs need to compare byte reads with `UInt8` literals without converting through `Nat`.  At this checkpoint, the extractor admitted `UInt8` as a local scalar type while keeping `UInt8` out of the exported function ABI.  `OfNat UInt8` and `UInt8.ofNat` lower modulo `256`, matching Lean evaluation for values such as `(300 : UInt8).toNat = 44`.

`LeanExe.Examples.ByteArrayPrograms.firstByteIsStar` checks a `ByteArray.get!` result against `(42 : UInt8)`.  `LeanExe.Examples.Correctness.wrappedUInt8Literal` covers literal wrapping, and `uint8OfNatValue` covers runtime bounded-`Nat` conversion through `UInt8.ofNat`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 52 accepted, 11 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 6 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke wrappedUInt8Literal .lake/build/core-correctness/wrappedUInt8Literal.wasm` returned `44`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8OfNatValue .lake/build/core-correctness/uint8OfNatValue.wasm 298` returned `43`.

## 2026-05-06: Internal UInt8 Helper Signatures

The compiler now separates exported entry ABI support from project-local helper support.  Exported entries still rejected `UInt8` parameters and results at this checkpoint, because the public ABI had not assigned byte-sized scalar slots.  Internal helpers may use `UInt8` parameters and results, and the lowering represents those values as scalar `i64` slots constrained by the operations that produce them.  The later public `UInt8` and `UInt32` ABI entry supersedes this boundary.

`LeanExe.Examples.ByteArrayPrograms.nextByte` takes and returns `UInt8`.  `firstByteNextIsZero` calls it on a `ByteArray.get!` result and checks the modulo-256 wrap from `255` to `0`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 52 accepted, 13 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 9 bytearray allocation cases`.

## 2026-05-06: UInt8 Arithmetic Wrapping

Accepting internal `UInt8` values made the previous generic lowering of `HAdd`, `HSub`, and `HMul` too broad.  Those primitives reused the `UInt64` operations unless the result type was `Nat`, which would compile `(255 : UInt8) + 1` as `256` instead of `0`.  The extractor now inspects the primitive result type and masks `UInt8` addition, subtraction, and multiplication to eight bits.

`UInt8` division and remainder already match Lean under the existing checked unsigned lowering for zero divisors: `x / 0` returns `0`, and `x % 0` returns `x`.  `LeanExe.Examples.Correctness.uint8AddWrap`, `uint8SubWrap`, `uint8MulWrap`, and `uint8DivModZero` cover these cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 56 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8AddWrap .lake/build/core-correctness/uint8AddWrap.wasm` returned `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8SubWrap .lake/build/core-correctness/uint8SubWrap.wasm` returned `255`.

## 2026-05-06: Bool Pattern Matching

The generic extractor now lowers `Bool.casesOn` and generated `match_*` declarations whose scrutinee type is `Bool`.  Earlier matcher recognition treated every generated matcher as an `Option` matcher, which caused Bool matches to fail while trying to read scalar values as `Option` tags.  The extractor now classifies generated matchers by the scrutinee type in the checked matcher declaration before choosing the Bool or Option lowering.

Bool matches use the existing conditional IR and preserve branch laziness, so a skipped match arm may contain a partial expression such as an out-of-bounds array access.  Structured match results use the same extractor-level `valueIte` path as structured `if` expressions.

`LeanExe.Examples.Correctness.boolMatchScalar`, `boolMatchSkipsTrap`, `boolMatchCondition`, and `boolMatchProduct` cover scalar results, branch laziness, boolean-valued matches used as conditions, and product-valued match results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 63 accepted, 13 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 9 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolMatchSkipsTrap .lake/build/core-correctness/boolMatchSkipsTrap.wasm` returned `7`.

## 2026-05-06: Decidable Comparison Booleans

Lean programs often use `decide` to turn a decidable proposition into a `Bool`.  The extractor now recognizes `Decidable.decide` when the proposition is already in the supported condition fragment, such as bounded `Nat` or `UInt64` comparisons.  Unsupported propositions still fail through the existing condition extractor rather than receiving a broad or guessed lowering.

`LeanExe.Examples.Correctness.decideNatLt` covers a `Nat` comparison used as an `if` condition through `decide`, and `decideUInt64Ge` covers a `Bool` result produced directly from a decided `UInt64` comparison.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 67 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke decideUInt64Ge .lake/build/core-correctness/decideUInt64Ge.wasm 3` returned `1`.

## 2026-05-06: Scalar Propositional Equality

The condition extractor now supports `Eq` propositions over admitted scalar runtime types: `Bool`, `UInt8`, `UInt64`, and bounded `Nat`.  This admits ordinary Lean forms such as `if x = 3 then ...` and `decide (x = 3)` without requiring source code to use `==`.  Equality over structured values remains unsupported until those values have an explicit equality lowering.

`LeanExe.Examples.Correctness.propEqNat` covers direct propositional equality in an `if`, `decideEqUInt64` covers equality through `Decidable.decide`, and `propEqBoolSkipsTrap` checks that equality against `true` still preserves short-circuit evaluation inside the boolean expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 72 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propEqBoolSkipsTrap .lake/build/core-correctness/propEqBoolSkipsTrap.wasm` returned `1`.

## 2026-05-06: Proposition Connectives

The condition extractor now supports proposition-level `And`, `Or`, `Not`, `True`, and `False` when their subconditions are already in the supported fragment.  This admits source forms such as `if x > 1 ∧ x < 5 then ...` and `decide (x < 2 ∨ x > 5)`.  The lowering uses the same short-circuiting condition IR as boolean `&&` and `||`.

`LeanExe.Examples.Correctness.propAndNat`, `propOrNat`, and `propNotNat` cover compound `Nat` propositions.  `propOrSkipsTrap` and `propAndSkipsTrap` check that proposition connectives do not evaluate skipped branches containing partial array reads.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 81 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propOrSkipsTrap .lake/build/core-correctness/propOrSkipsTrap.wasm` returned `1`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propAndSkipsTrap .lake/build/core-correctness/propAndSkipsTrap.wasm` returned `0`.

## 2026-05-06: Scalar Min and Max

The extractor now lowers `Min.min` and `Max.max` for bounded `Nat`, `UInt8`, and `UInt64`.  The lowering uses unsigned scalar comparisons over the existing runtime representation.  This keeps `Nat.min` and `Nat.max` inside the bounded fragment and gives byte and word-sized code the usual scalar selection operations.

`LeanExe.Examples.Correctness.natMinMax`, `u64MinMax`, and `u8MinMax` cover the supported types.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 86 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke u8MinMax .lake/build/core-correctness/u8MinMax.wasm` returned `280`.

## 2026-05-06: Bitwise Operator Notation

The extractor now lowers `HAnd.hAnd`, `HOr.hOr`, and `HXor.hXor` for `UInt64` and internal `UInt8` values.  Lean elaborates the `&&&`, `|||`, and `^^^` notations through those typeclass operations, while earlier examples used the direct `UInt64.land`, `UInt64.lor`, and `UInt64.xor` functions.

`LeanExe.Examples.Correctness.bitwiseNotation` covers the notation path and returns the same result as the direct-call `bitwiseOrXor` example.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 87 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bitwiseNotation .lake/build/core-correctness/bitwiseNotation.wasm` returned `6`.

## 2026-05-06: Shift Operator Notation

The extractor now lowers `HShiftLeft.hShiftLeft` and `HShiftRight.hShiftRight` for `UInt64`.  Lean elaborates `<<<` and `>>>` through those typeclass operations, while existing coverage used direct `UInt64.shiftLeft` and `UInt64.shiftRight` calls.

`LeanExe.Examples.Correctness.shiftNotation` covers the notation path and keeps the existing shift-count masking expectation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 88 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke shiftNotation .lake/build/core-correctness/shiftNotation.wasm` returned `42`.

## 2026-05-06: Bitwise Complement

The extractor now lowers `Complement.complement` for `UInt64` and internal `UInt8` values.  `UInt64` complement lowers to xor with `2^64 - 1`; `UInt8` complement lowers to xor with `255`.  The primitive application code also now isolates inline calls, emitted calls, unary primitives, and binary primitives in separate helper functions, which keeps additional primitive cases out of the main expression matcher.

`LeanExe.Examples.Correctness.complementNotation` covers `~~~` on `UInt64`, and `u8Complement` covers the internal `UInt8` path.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 90 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke complementNotation .lake/build/core-correctness/complementNotation.wasm` returned `255`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke u8Complement .lake/build/core-correctness/u8Complement.wasm` returned `255`.

## 2026-05-06: Byte UInt8 Bitwise Coverage

`firstByteLowNibble` exercises `UInt8` bitwise notation on a value returned by `ByteArray.get!`.  This covers the path real byte-oriented code uses: host input enters memory, `ByteArray.get!` produces an internal `UInt8`, and `&&&` lowers through `HAnd.hAnd` without converting through `Nat`.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 12 bytearray allocation cases`.

## 2026-05-06: ByteArray.isEmpty

The extractor now lowers `ByteArray.isEmpty` to a length comparison against zero.  This is the same value already available through the `ByteArray` parameter ABI, so it adds a source-level convenience without changing the memory representation.

`LeanExe.Examples.ByteArrayPrograms.emptyViaIsEmpty` covers the new primitive in the byte-array allocation harness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 14 bytearray allocation cases`.

## 2026-05-06: ByteArray Bang Indexing

`input[i]!` for `ByteArray` elaborates through `GetElem?.getElem!`, not `ByteArray.get!`.  The extractor now distinguishes the receiver type for `GetElem?.getElem!` and lowers `ByteArray` receivers to the byte-array bounds check and `i32.load8_u` path.  `Array UInt64` receivers continue to use the existing array load path.

`LeanExe.Examples.ByteArrayPrograms.firstByteBangIndex` covers empty input and two byte values through the byte-array allocation harness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 17 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`.

## 2026-05-06: Mixed ByteArray and Scalar ABI

`LeanExe.Examples.ByteArrayPrograms.byteAtOrZero` takes a `ByteArray` followed by a bounded `Nat` index.  This checks that the flattened byte-array ABI slots `(ptr, len)` compose with later scalar parameters in the exported Wasm signature.  The host calls the compiled function as `(ptr, len, index)`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 20 bytearray allocation cases`.

## 2026-05-06: Array.isEmpty

The extractor now lowers `Array.isEmpty` for `Array UInt64` by reading the array header length and comparing it with zero.  This matches the existing memory layout and avoids requiring source programs to write `a.size == 0`.

`LeanExe.Examples.Correctness.arrayIsEmptyValues` checks both empty and non-empty arrays.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 91 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayIsEmptyValues .lake/build/core-correctness/arrayIsEmptyValues.wasm` returned `1`.

## 2026-05-06: Array.back!

The extractor now lowers `Array.back!` for `Array UInt64`.  It evaluates the array expression once, binds the array pointer in a local, computes `size - 1`, and reuses the existing bounds-checked array load.  Empty arrays therefore trap through the same `unreachable` path as an out-of-bounds indexed read.

`LeanExe.Examples.Correctness.arrayBackRead` covers the non-empty case.  `arrayBackEmptyTrap` compiles but must trap at runtime.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 92 accepted, 13 rejected, and 3 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayBackRead .lake/build/core-correctness/arrayBackRead.wasm` returned `9`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayBackEmptyTrap .lake/build/core-correctness/arrayBackEmptyTrap.wasm` trapped with `wasm unreachable`.

## 2026-05-06: Array.getD

The extractor now lowers `Array.getD` for `Array UInt64`.  It binds the array pointer and index once, checks the index against the header length, and returns either the bounds-checked load or the default expression.  The default expression stays in the else branch, so an in-bounds read does not evaluate a default that would trap.

`LeanExe.Examples.Correctness.arrayGetDRead` covers in-bounds and out-of-bounds reads.  `arrayGetDSkipsDefaultTrap` checks default-branch laziness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayGetDRead .lake/build/core-correctness/arrayGetDRead.wasm 2` returned `99`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayGetDSkipsDefaultTrap .lake/build/core-correctness/arrayGetDSkipsDefaultTrap.wasm` returned `5`.

## 2026-05-06: Combined Correctness Runner

`test/run_all.js` runs the current local correctness suite: `lake build`, `test/core_correctness.js`, `test/bytearray_alloc.js`, and `test/fuzz_validate.js`.  The fuzz case count defaults to `50` and can be changed through `LEANEXE_FUZZ_CASES`.  The runner uses `LEAN_WASM_EXE` when set, matching the existing harnesses.

Checks run:

- [x] `node test/run_all.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`, `checked 14 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Scalar Then ByteArray ABI

`LeanExe.Examples.ByteArrayPrograms.prefixPlusFirstByte` takes a scalar `UInt64` before a `ByteArray`.  This checks the other mixed-parameter order for the flattened byte-array ABI: the exported Wasm function receives `(prefix, ptr, len)`.  The prior byte-array harness covered `(ptr, len, scalar)`, so the test suite now exercises both sides of the source-order rule.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 23 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt8 Shifts

The extractor now lowers `UInt8` shift notation and the direct `UInt8.shiftLeft` and `UInt8.shiftRight` functions.  Lean’s `UInt8` shift semantics mask the shift count modulo eight.  Left shifts also wrap the result to eight bits.  The lowering implements that rule with an explicit `count &&& 7` expression and the existing `UInt8` result mask.

`LeanExe.Examples.Correctness.uint8ShiftNotation` covers `<<<` and `>>>` notation.  `uint8DirectShift` covers the named functions, including an overflowing left shift and a right shift whose count equals eight.  Both examples return `Nat` values so the current public ABI remains unchanged.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 97 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 97 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array.append

The IR now has an `arrayAppend` expression for `Array UInt64`.  The extractor lowers `Array.append` by evaluating both array arguments once and passing their pointers to that IR expression.  CoreWasm allocates a fresh array, stores the combined length, copies the left cells, and then copies the right cells at an offset equal to the left length.

This implementation follows the same conservative copy-on-write discipline as `Array.set!`, `Array.push`, and nonempty `Array.pop`.  Old aliases keep observing the old arrays.  The WAT printer now has the same append lowering as the binary emitter, and the Wasmtime WAT check covers the generated text path.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 99 accepted, 13 rejected, and 3 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayAppendRead --out .lake/build/core-correctness/arrayAppendRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayAppendRead .lake/build/core-correctness/arrayAppendRead.wat` returned `11223344`.
- [x] `node test/run_all.js` returned `checked 99 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.getD

The extractor now lowers `Option.getD` for first-fragment payloads.  It reuses the existing extractor-level tag and payload representation, returning the default value when the tag is zero and the payload otherwise.  The default expression remains inside the `none` branch of the emitted value, so a default that would trap is skipped when the option is `some`.

`LeanExe.Examples.Correctness.optionGetDNone` covers the `none` branch.  `optionGetDSomeSkipsDefaultTrap` checks default laziness with an empty-array `back!` expression.  `optionGetDProduct` checks that structured product payloads pass through the same lowering before projection.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 102 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 102 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Tag Tests

The extractor now lowers `Option.isSome` and `Option.isNone`.  Both operations inspect only the extractor-level tag and return a scalar `Bool`.  The payload expression is left unused, so a `some` payload that would trap is not evaluated by a tag test.

`LeanExe.Examples.Correctness.optionIsSomeSkipsPayloadTrap` checks that payload laziness.  `optionIsNoneValues` covers both `none` and `some` values in a boolean condition.  These cases keep `Option` inside the existing internal structured-value representation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 104 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 104 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.elim

The extractor now lowers `Option.elim` for first-fragment result values.  The lowering extracts the option tag and payload, then emits the default arm for `none` and the function arm for `some`.  Both arms remain branch-local in the emitted value, so the default expression is skipped for `some` and the function body is skipped for `none`.

`LeanExe.Examples.Correctness.optionElimSomeSkipsDefaultTrap` checks the skipped-default case.  `optionElimNoneSkipsSomeArmTrap` checks the skipped-function case.  `optionElimProduct` checks a product result, which exercises the structured-value branch path rather than only scalar extraction.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 107 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 107 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.map

The extractor now lowers `Option.map` when the mapping function is a one-argument lambda and the result type remains inside the first fragment.  The result keeps the original option tag.  The mapped payload is emitted only for the `some` branch, while the `none` branch uses the default payload for the mapped result type.

`LeanExe.Examples.Correctness.optionMapSome` covers a scalar mapped value.  `optionMapNoneSkipsFunctionTrap` checks that the mapping function is not evaluated for `none`.  `optionMapProduct` checks a structured product result inside an `Option`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 110 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 110 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.bind

The extractor now lowers `Option.bind` when the bind function is a one-argument lambda returning a supported `Option` value.  If the input option is `none`, the result tag is `none` and the bind function body is not emitted on the executed path.  If the input option is `some`, the result takes the tag and payload produced by the bind function.

`LeanExe.Examples.Correctness.optionBindSome` covers the ordinary `some` case.  `optionBindNoneSkipsFunctionTrap` checks that the bind function is skipped for `none`.  `optionBindFunctionNone` and `optionBindProduct` cover a function that returns `none` and a function that returns an `Option` carrying a product.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 114 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 114 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array.extract

The IR now has an `arrayExtract` expression for `Array UInt64`.  The extractor lowers `Array.extract` by evaluating the array, start index, and stop index once.  CoreWasm clamps stop to the source length, computes a zero result length when the effective stop is not greater than start, allocates a fresh array, and copies the selected cells from `start + i` into result cell `i`.

`LeanExe.Examples.Correctness.arrayExtractRead` covers an ordinary interior slice.  `arrayExtractClamps` covers stop clamping, start past the end, and stop before start.  The WAT path is checked with Wasmtime for the clamping case because this feature adds a new text-emitter branch as well as a binary-emitter branch.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 116 accepted, 13 rejected, and 3 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayExtractClamps --out .lake/build/core-correctness/arrayExtractClamps.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayExtractClamps .lake/build/core-correctness/arrayExtractClamps.wat` returned `340`.
- [x] `node test/run_all.js` returned `checked 116 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat.succ and Nat.pred

The extractor now lowers direct `Nat.succ` and `Nat.pred` applications.  `Nat.succ` uses the existing checked bounded-`Nat` addition operation with an increment of one, so it traps when the result would exceed the current `i64` representation.  `Nat.pred` uses the existing bounded-`Nat` subtraction operation with a decrement of one, so predecessor at zero returns zero.

`LeanExe.Examples.Correctness.natSuccPred` covers normal successor and predecessor behavior at `5` and the predecessor-at-zero case.  `natSuccOverflow` compiles and traps at runtime, matching the bounded-`Nat` overflow policy used by addition.  This change adds source coverage for code that uses the named `Nat` operations instead of arithmetic notation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 118 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 118 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Fixed-Width Scalar Conversions

The extractor now lowers `Nat.toUInt64`, `UInt64.toUInt8`, and `UInt8.toUInt64`.  `Nat.toUInt64` follows the same rule as `UInt64.ofNat`: bounded runtime `Nat` values pass through unchanged, and direct literals lower modulo `2^64` instead of going through bounded-`Nat` literal rejection.  `UInt64.toUInt8` masks to eight bits, while `UInt8.toUInt64` preserves the current scalar representation.

`LeanExe.Examples.Correctness.natToUInt64Value` covers a runtime bounded `Nat` conversion, and `natToUInt64Huge` covers the direct large-literal case.  `uint64ToUInt8Wrap` checks byte masking from `300` to `44`.  `uint8ToUInt64Value` checks widening from `UInt8` before `UInt64` arithmetic.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 122 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 122 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Literals

The extractor now lowers `List.toArray` when its argument is a literal `List UInt64`.  This accepts Lean array literal syntax such as `#[]` and `#[10, 20, 30]` without adding general list support.  The lowering allocates an array of the literal length, then uses the existing copy-on-write `arraySet` expression to populate each literal element in source order.

`LeanExe.Examples.Correctness.arrayLiteralRead` covers a nonempty literal.  `arrayEmptyLiteral` covers the empty literal.  The implementation rejects nonliteral lists and non-`UInt64` item types rather than inferring behavior for general `List.toArray`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 124 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 124 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal UInt32

The extractor now admits `UInt32` as an internal scalar type.  It keeps the public ABI unchanged: exported `UInt32` parameters and results are still rejected.  Local values and helper signatures can use `UInt32`, represented as an `i64` whose producing operations constrain the value to `0..2^32-1`.

The lowering follows Lean’s fixed-width behavior.  `UInt32` literals and `UInt32.ofNat` lower modulo `2^32`, `UInt64.toUInt32` masks to 32 bits, and `UInt32.toNat` and `UInt32.toUInt64` preserve the constrained representation.  Addition, subtraction, multiplication, bitwise operations, complement, shifts, `min`, and `max` now have `UInt32` cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 132 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 132 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt8 and UInt32 Conversions

The extractor now lowers `UInt8.toUInt32` and `UInt32.toUInt8`.  Widening from `UInt8` to `UInt32` preserves the constrained scalar representation.  Narrowing from `UInt32` to `UInt8` masks to eight bits, matching Lean’s fixed-width conversion behavior.

`LeanExe.Examples.Correctness.uint8ToUInt32Value` checks widening before `UInt32` arithmetic.  `uint32ToUInt8Wrap` checks narrowing from `300` to `44`.  These conversions stay internal because exported `UInt8` and `UInt32` values remain outside the ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 134 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 134 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Recursion Branch Orientation

The Nat-recursion extractor now accepts the conditional tail-call shape with the recursive call in either branch.  For `if cond then recursiveCall else exitValue`, the emitted loop continues while `cond` holds and fuel remains.  For the older `if cond then exitValue else recursiveCall` shape, the emitted loop continues while `cond` is false and fuel remains.

`LeanExe.Examples.Correctness.recThenBranchExitDemo` covers early exit from the new orientation.  `recThenBranchFuelDemo` covers fuel exhaustion in the same source shape.  Existing recursion examples still cover unconditional tail calls, let-bound recursive arguments, product-valued recursive arguments, and the original early-exit orientation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: ByteArray FNV-1a Example

`LeanExe.Examples.ByteArrayPrograms.fnv1a32` computes the 32-bit FNV-1a checksum of a read-only `ByteArray` and returns it as `UInt64` at the public ABI boundary.  The program uses internal `UInt8` reads, `UInt8.toUInt32`, internal `UInt32` xor and multiplication, and the supported fuel-recursion shape over a byte buffer.  This gives the byte-array harness a small real byte-oriented program rather than only single-byte accessors.

The JavaScript harness computes expected values with `Math.imul` and unsigned 32-bit truncation.  The cases cover empty input, one byte, and a short multi-byte input.  The Lean program remains pure and does not add byte-array construction or mutation support.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 26 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Scalar Inequality

The extractor now lowers Lean’s `!=` notation, which elaborates to `bne`.  The lowering is the negation of the same scalar equality path used for `BEq.beq`.  It works both as a `Bool` expression and directly as a condition.

`LeanExe.Examples.Correctness.bneScalars` covers `UInt64` inequality in a branch.  `bneAsBool` covers a `Bool` entry result over bounded `Nat`.  `bneBool` covers inequality over `Bool` values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 141 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 141 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool.xor

The extractor now lowers `Bool.xor` through the condition extractor.  The lowering computes exclusive-or from existing condition forms: left and not right, or not left and right.  This keeps boolean normalization in the same path used by `&&`, `||`, and `!`.

`LeanExe.Examples.Correctness.boolXorValues` covers false/false, false/true, and true/true cases.  The entry returns `Bool`, so the harness checks the public boolean ABI as well as condition lowering.  No new IR operation was needed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 144 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 144 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Safe Indexing

The extractor now lowers `GetElem?.getElem?`, the elaborated form of `a[i]?`, for `Array UInt64` and `ByteArray`.  The lowering adds extractor-level structured lets so the array pointer, byte-array pointer and length, and index are bound once around the resulting `Option` tag and payload.  The `some` payload uses the existing bounds-checked load, but consumers only evaluate that payload when the tag is nonzero, so out-of-bounds safe indexing returns `none` without trapping.

This work also fixes generated `Option` matcher arm ordering.  Generated matcher declarations pass arms in source order, so a match written with the `some` arm first does not have the same argument order as a match written with the `none` arm first.  The extractor now classifies generated `Option` matcher arms by the lambda domain: `Unit` for `none`, and the payload type for `some`.

`LeanExe.Examples.Correctness.arrayGetQuestionRead` covers in-bounds and out-of-bounds `Array UInt64` safe indexing.  `arrayGetQuestionGetDSkipsDefaultTrap` checks default laziness after safe indexing.  `arrayGetQuestionNoneSkipsPayloadTrap` checks that the out-of-bounds path does not execute the payload load.  `optionSomeFirstMatch` directly covers generated `Option` matcher arm ordering.  `LeanExe.Examples.ByteArrayPrograms.byteAtQuestionOrZero` covers safe byte indexing through the byte-array ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 149 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 29 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 149 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool Matcher Arm Order

Generated `Bool` matcher declarations pass arms in source order.  The extractor previously assumed the generated argument order was always false arm then true arm, which only holds when the source match lists `false` first.  The extractor now reads the generated matcher type and classifies each arm by whether its result type is indexed by `Bool.false` or `Bool.true`.

`LeanExe.Examples.Correctness.boolMatchTrueFirstScalar` covers a match written with the `true` arm first.  `boolMatchTrueFirstSkipsFalseTrap` checks branch laziness in the same source order, so a reversed lowering would execute the false arm and trap.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 152 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 152 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nonrecursive Nat Matches

The extractor now lowers nonrecursive zero/successor matches over bounded `Nat` values.  Generated `Nat` matchers have a `Unit` arm for zero and a `Nat` arm for successor, so the extractor classifies source-ordered arms by binder type.  The lowering binds the scrutinee once, returns the zero arm when it is zero, and passes `n - 1` to the successor arm when it is nonzero.

`LeanExe.Examples.Correctness.natMatchZero` covers the ordinary zero-first source order.  `natMatchSuccFirst` covers successor-first source order and checks that the predecessor value reaches the successor arm.  `natMatchZeroSkipsSuccTrap` and `natMatchSuccSkipsZeroTrap` check branch laziness.  `natMatchBoolCondition` covers a `Nat` match producing `Bool`, and `natMatchProduct` covers a structured product result.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 162 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 162 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Classifier Alignment

The checked-environment report now uses the generic entry signature checker to render entry shapes instead of a small hard-coded set of shapes.  It also classifies implemented frontier primitives for internal products, internal `Option`, erased `Unit` values used by generated matchers, safe indexing, array append and extract, fixed-width conversions, and nonrecursive `Nat` matches.  This removes rejected frontier entries from reports for declarations that the compiler already accepts.

`test/report_classification.js` covers one `Nat` matcher entry, one byte-array safe-indexing entry, and one `Option`/product entry.  Each case checks that the report shows the expected entry shape, reports an implemented compile status, and contains no rejected frontier item.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 3 report classification cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 162 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal Unit Values

The generic compiler now admits `Unit` as an internal value type.  It represents `()` as scalar zero, accepts local `Unit` values, product fields containing `Unit`, and project-local helpers with `Unit` parameters or results.  The public ABI remains unchanged: entries with `Unit` parameters or `Unit` results are rejected.

`LeanExe.Examples.Correctness.unitProductSecond` covers `Unit` inside a product.  `unitHelperCall` covers an internal helper parameter of type `Unit`, and `unitResultIgnored` covers an internal helper result of type `Unit`.  `rejectUnitReturn` and `rejectUnitParam` keep the ABI boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 165 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 165 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt32 Division Coverage

The generic primitive path already lowered `UInt32` division and remainder through the same checked division and remainder operations used by `UInt64` and `UInt8`.  The specification did not state that support, and the correctness harness did not test it.  The tests now cover ordinary `UInt32` division and remainder and Lean’s zero-divisor behavior.

`LeanExe.Examples.Correctness.uint32DivMod` checks a nonzero divisor.  `uint32DivModZero` checks that `x / 0` returns `0` and `x % 0` returns `x`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 167 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 167 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Dependent If

The extractor now lowers `dite`, the elaborated form of `if h : p then ... else ...`.  The condition uses the existing proposition extractor, and both proof-lambda arms receive an erased scalar placeholder for the proof binder.  The emitted value uses the same branch-local behavior as ordinary `if`, so skipped dependent-if arms do not evaluate partial operations.

`LeanExe.Examples.Correctness.dependentIfNat` covers a bounded-`Nat` proposition.  `dependentIfSkipsElseTrap` and `dependentIfSkipsThenTrap` check branch laziness.  `dependentIfProduct` covers a structured product result.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 173 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 173 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Empty Constructors

The extractor now lowers `Array.empty`, `Array.mkEmpty`, `Array.emptyWithCapacity`, and `Array.singleton` for `Array UInt64`.  Empty constructors allocate an empty array.  The capacity argument is not extracted because the current array layout has no observable capacity, and Lean’s pure definitions of these constructors do not use that argument.  `Array.singleton` allocates one element through the existing replicate path.

`LeanExe.Examples.Correctness.arrayEmptyConstructors` covers the three empty constructors.  `arrayEmptyCapacitySkipsTrap` checks that an ignored capacity expression is not evaluated.  `arraySingletonRead` checks singleton size and element contents.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 176 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 176 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: ByteArray Extract

The extractor now lowers `ByteArray.extract` as an internal read-only slice.  It binds the source pointer, source length, start, and stop once, clamps stop to the source length, returns an empty slice when start is outside the source or stop does not exceed start, and otherwise returns a pointer-length view into the original bytes.  Public `ByteArray` results remain outside the ABI.

`LeanExe.Examples.ByteArrayPrograms.sliceSecondPlusSize` checks reading through a nonempty slice and the empty result when start equals the source length.  `sliceClampSize` checks stop clamping, and `sliceStopBeforeStart` checks the empty case when stop precedes start.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 34 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 176 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Division Coverage

The extractor already lowered `Nat` division and remainder through the checked unsigned operation path.  The specification now states that bounded `Nat` division and remainder use Lean’s zero-divisor behavior: `x / 0` returns `0`, and `x % 0` returns `x`.

`LeanExe.Examples.Correctness.natDivModNormal` checks ordinary quotient and remainder results.  `natDivModZero` checks the zero-divisor case.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 179 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 179 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Product Pattern Matching

The extractor now lowers product pattern matching for ordinary generated matchers and direct `Prod.casesOn` applications, and it recognizes `Prod.rec` if a checked term contains it.  A product matcher arm receives the left and right fields as internal values, preserving the same field-level laziness used by product projection.  The demand summary path maps demanded arm binders back to the corresponding scrutinee fields, so a helper that destructures a pair and ignores one field does not force the ignored field.

`LeanExe.Examples.Correctness.productMatchDestructure` checks ordinary pair destructuring.  `productMatchUsesFirstOnly` checks that the ignored field does not trap.  `productMatchCondition` checks a product match used as a condition, and `productMatchNested` checks a product match returning a product.

An initial parallel `node test/core_correctness.js` run raced `lake build LeanExe.Examples.Correctness` and failed before compilation because the example module’s `.olean` file was not present.  The harness passed when rerun after the example build completed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 183 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 183 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Fallback

The extractor now lowers `Option.orElse` and option `<|>` for internal `Option` values.  The fallback thunk receives an erased `Unit` value and is extracted only for the `none` arm.  The demand summary path treats the fallback as branch-local, so a helper that returns an existing `some` value does not force a trapping fallback.

`LeanExe.Examples.Correctness.optionOrElseNone` checks `<|>` on `none`.  `optionOrElseDirectSomeSkipsFallbackTrap` checks direct `Option.orElse` on `some` without evaluating the fallback, and `optionOrElseProduct` checks a structured payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 186 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 186 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Filter

The extractor now lowers `Option.filter` for internal `Option` values.  The predicate runs only for `some`, and it receives the payload as a lazy internal value.  Filtering a `some` value to `none` leaves the payload irrelevant, matching the existing tagged representation.

`LeanExe.Examples.Correctness.optionFilterSomeKeep` and `optionFilterSomeDrop` check the two predicate outcomes for `some`.  `optionFilterNoneSkipsPredicateTrap` checks that `none` skips a trapping predicate.  `optionFilterIgnoresPayloadTrap` checks that a predicate which ignores its argument does not force a trapping payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 190 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 190 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Structured Helper Inlining

Nonrecursive project-local helpers now inline directly from the checked environment when their source signature uses supported local types.  This separates helper inlining from the Wasm function list, whose emitted functions still use the scalar and array ABI.  The inline stack rejects recursive inline expansion, so recursive code continues through the existing recursion path rather than expanding without a bound.

`LeanExe.Examples.Correctness.productHelperResult` checks a helper returning a product, and `productHelperParamSkipsTrap` checks a product parameter with an ignored trapping field.  `optionHelperResult` and `optionHelperNone` check a helper returning `Option`, and `optionHelperParam` checks an `Option` parameter.

The first focused harness run failed on `productHelperResult` because the inline attempt still lived only in the scalar extraction path.  The value extractor now tries local helper inlining before falling back to scalar extraction, so structured helper results enter the extractor as structured values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 195 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 195 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal Except Values

The extractor now lowers restricted internal `Except` values.  `Except.error` uses tag `0`, `Except.ok` uses tag `1`, and each value carries both an error payload and an ok payload so pattern matching can select the demanded arm.  `Except Unit α` remains rejected because the current internal type shape also represents `Option α` as `Unit ⊕ α`; the extractor needs source type identity before those two cases can share the same payload types without ambiguity.

`LeanExe.Examples.Correctness.exceptOkMatch`, `exceptOkFirstMatch`, and `exceptErrorMatch` check constructor ordering and generated matcher arm ordering.  `exceptErrorSkipsUnusedPayloadTrap` checks payload laziness, `exceptMatchCondition` checks a match used as a condition, and `exceptProductPayload` checks a structured ok payload.  `rejectExceptReturn` and `rejectExceptParam` keep the current ABI boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 201 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 201 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Map and Bind

The extractor now lowers `Except.map` and `Except.bind` for restricted internal `Except` values.  Both operations evaluate their function only for the `ok` case.  `Except.bind` preserves an existing error without evaluating the bind function, and it adopts the tag and payloads returned by the bind function for `ok`.

`LeanExe.Examples.Correctness.exceptMapOk`, `exceptMapErrorSkipsFunctionTrap`, and `exceptMapProduct` check mapping over `ok`, skipped mapping over `error`, and structured mapped payloads.  `exceptBindOk`, `exceptBindErrorSkipsFunctionTrap`, `exceptBindFunctionError`, and `exceptBindProduct` cover the corresponding bind cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 208 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 208 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Coverage for Structured Values

The report classification harness now includes entries that depend on structured helper inlining and restricted internal `Except` support.  `productHelperResult` checks an inline-only product helper signature, and `exceptBindProduct` checks the `Except` constructors, matcher, and bind classifier path.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 5 report classification cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 208 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Helper Coverage

The correctness suite now covers nonrecursive helpers with restricted `Except` parameters and results.  The specification also no longer describes structured outputs as waiting for `Except` to enter the core IR; `Except` is internal now, while public structured outputs still need a Wasm result ABI.

`LeanExe.Examples.Correctness.exceptHelperResult` and `exceptHelperError` check a helper returning restricted `Except`.  `exceptHelperParam` checks an `Except` parameter.

The first focused harness run failed on `exceptHelperResult` because the value-level `if` extractor still handled only ByteArray, product, and `Option`-shaped sum result types before falling back to scalar extraction.  The value-level `if` path now accepts every supported local result type.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 211 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 211 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except toOption

The extractor now lowers `Except.toOption` for restricted internal `Except` values.  The lowering reuses the `Except` tag as the `Option` tag and keeps only the ok payload, so an error payload is not needed when the resulting `Option` is inspected.

`LeanExe.Examples.Correctness.exceptToOptionOk` checks the ok path.  `exceptToOptionErrorSkipsPayloadTrap` checks that converting an error to `none` does not force an ignored trapping error payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 213 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 213 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Fallback

The extractor now lowers `<|>` for restricted internal `Except` values through `HOrElse.hOrElse`.  The fallback thunk runs only for `error`; an existing `ok` value preserves its payload without evaluating the fallback.

`LeanExe.Examples.Correctness.exceptOrElseError` checks recovery from an error, `exceptOrElseOkSkipsFallbackTrap` checks fallback laziness for `ok`, and `exceptOrElseFallbackError` checks a fallback that also returns an error.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 216 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 216 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Unit Rejection

The correctness suite now checks the documented rejection of `Except Unit α`.  The current internal type representation uses `Unit ⊕ α` for `Option α`, so accepting `Except Unit α` would require the extractor to preserve source type identity rather than relying on the current structural sum type alone.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 216 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 216 accepted, 20 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Specification Alignment

Several summary rows in `spec.md` still described only product and `Option` support after restricted `Except` entered the internal value fragment.  The summary rows now mention restricted `Except` for local lets, constructors, pattern matching, and report classification.

Checks run:

- [x] Documentation-only change; no build required.

## 2026-05-07: Proof-Indexed GetElem

The extractor now lowers `GetElem.getElem`, the checked term behind proof-indexed `a[i]` and `input[i]`.  The proof argument is erased, and the runtime load uses the same checked array or byte-array load path as partial indexing.  This lets source code use ordinary proof-indexed indexing when Lean can supply or carry the bounds proof.

`LeanExe.Examples.Correctness.arrayGetProof` checks `Array UInt64` proof-indexed reads.  `LeanExe.Examples.ByteArrayPrograms.byteAtProofOrZero` checks proof-indexed `ByteArray` reads under a dependent-if bounds proof.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 217 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 36 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 217 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Run

The extractor now erases `Id.run` and `Pure.pure` when the monad argument is `Id`.  This supports simple pure `do` blocks that elaborate to `Id.run do ... return value`.  General monadic bind, loops, and effectful `do` blocks remain outside this step.

`LeanExe.Examples.Correctness.idRunLet` checks a simple pure return.  `idRunSkipsUnusedLetTrap` checks that the existing lazy-let behavior still skips an unused trapping binding inside the `Id` block.  `idRunCondition` checks a pure `Id` block used as a condition.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 220 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 220 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Bind

The extractor now erases `Bind.bind` when the monad argument is `Id`.  The bound value enters the continuation as a lazy internal value, matching the extractor’s existing lazy-let behavior for ignored bindings.  This supports simple pure `do` blocks with `let x ← pure value`.

`LeanExe.Examples.Correctness.idRunBind` checks a pure bind in an `Id.run` block.  `idRunBindSkipsUnusedTrap` checks that an ignored bound value does not force a trapping expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 222 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 222 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Coverage for Pure Id

The report classification harness now includes `LeanExe.Examples.Correctness.idRunBind`, so the classifier checks the `Id.run`/`Pure.pure`/`Bind.bind` frontier used by simple pure `do` notation.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 6 report classification cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 222 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Simple let mut Coverage

Lean elaborates simple `let mut` assignment inside `Id.run` to ordinary shadowing lets, which the extractor already supports.  The correctness suite now covers that source style so it does not regress while pure `Id` support grows.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 223 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 223 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Loop Rejection

The correctness suite now checks that a pure `for` loop inside `Id.run` remains rejected.  Lean elaborates the loop body to a function that returns `ForInStep`, which the current extractor does not lower.  This keeps the pure `do` support limited to `Id.run`, `Pure.pure`, `Bind.bind`, and let-style code.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 223 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 223 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Structured Pure Id Bind Coverage

The correctness suite now covers `Id.run do let x ← pure ...` when the bound value is a product, an `Option`, or a restricted `Except`.  The extractor already routes `Id` binds through the general value extractor, so these tests confirm that pure `do` notation preserves the existing structured-value behavior instead of only scalar bindings.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 226 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 226 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except isOk

Lean 4.29 exposes `Except.isOk : Except ε α -> Bool`.  The extractor now lowers it for restricted internal `Except` values by reading the existing tag, so the payload of `Except.ok bad` is not extracted when the program only asks whether the value is ok.

An initial parallel `node test/report_classification.js` run raced `lake build LeanExe.Examples.Correctness` and failed because the example module’s `.olean` file was not present yet.  The report harness passed when rerun after the example build completed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 7 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 229 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 7 report classification cases`, `checked 229 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except mapError

Lean 4.29 exposes `Except.mapError : (ε -> ε') -> Except ε α -> Except ε' α`.  The extractor now lowers it for restricted internal `Except` values.  The mapping function runs only for `error`, and `ok` preserves its payload without evaluating the mapping function.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 8 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 232 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 8 report classification cases`, `checked 232 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt64 toNat Coverage

The correctness suite now covers `UInt64.toNat` directly and through method notation.  The method-notation case uses `UInt64` maximum to check that the bounded `Nat` representation preserves the full 64-bit value at the ABI boundary.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 234 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 8 report classification cases`, `checked 234 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option get!

Lean 4.29 defines `Option.get!` as a panic on `none`, not as an `Inhabited` default.  The IR now has an explicit trap expression, and the extractor lowers `Option.get!` by selecting the payload for `some` and the trap expression for `none`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 9 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 237 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 9 report classification cases`, `checked 237 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option any and all

The extractor now lowers `Option.any` and `Option.all` for internal `Option` values.  Both operations evaluate their predicate only for `some`; `any` returns false for `none`, and `all` returns true for `none`, matching Lean’s definitions.  The report classifier also recognizes `UInt64.decLt`, which appears as the decidable instance for a supported `UInt64` comparison inside an `Option.any` predicate.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 10 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 241 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 10 report classification cases`, `checked 241 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool toNat

The extractor now lowers `Bool.toNat`.  The current scalar representation already stores false as `0` and true as `1`, so the lowering preserves the existing expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 11 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 243 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 11 report classification cases`, `checked 243 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Boolean Comparisons

The extractor now lowers `Nat.blt` and `Nat.ble` as Boolean comparisons over the bounded `Nat` representation.  This covers code that calls the named Boolean comparison functions instead of using proposition comparisons in an `if`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 12 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 248 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 12 report classification cases`, `checked 248 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Boolean Equality

The extractor now lowers `Nat.beq` as Boolean equality over the bounded `Nat` representation.  The correctness suite covers both direct Bool results and conditions that branch on the named equality function.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 13 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 252 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 13 report classification cases`, `checked 252 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Append Notation

The extractor now lowers `HAppend.hAppend` for `Array UInt64`, so source code can use `left ++ right` instead of calling `Array.append` directly.  The lowering reuses the existing copy-on-write array append IR operation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 14 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 253 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 14 report classification cases`, `checked 253 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array back?

The extractor now lowers `Array.back?` for `Array UInt64`.  The emitted value is an internal `Option`: empty arrays produce `none`, and nonempty arrays produce `some` with the last element.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 15 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 255 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 15 report classification cases`, `checked 255 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array modify

The extractor now lowers `Array.modify` for `Array UInt64`.  In-bounds modification reads the old element, applies the source lambda, and emits the existing copy-on-write array update.  Out-of-bounds modification returns the original array and does not evaluate the lambda.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 16 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 257 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 16 report classification cases`, `checked 257 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array insertIdxIfInBounds

The extractor now lowers `Array.insertIdxIfInBounds` for `Array UInt64`.  The IR has a dedicated insertion expression so the emitter can evaluate the array and index first, then evaluate the inserted value only when `index <= size`.  In-bounds insertion allocates a fresh array, copies the prefix, writes the inserted value, and copies the suffix one slot to the right.  Out-of-bounds insertion returns the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 17 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 260 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayInsertIdxIfInBoundsSkipsValueTrap --out .lake/build/core-correctness/arrayInsertIdxIfInBoundsSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayInsertIdxIfInBoundsSkipsValueTrap .lake/build/core-correctness/arrayInsertIdxIfInBoundsSkipsValueTrap.wat` returned `7`.
- [x] `node test/run_all.js` returned `checked 17 report classification cases`, `checked 260 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array eraseIdxIfInBounds

The extractor now lowers `Array.eraseIdxIfInBounds` for `Array UInt64`.  In-bounds erasure allocates a fresh array with one fewer element, copies the prefix, and copies the suffix one slot to the left.  Out-of-bounds erasure returns the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 18 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 263 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayEraseIdxIfInBoundsMiddle --out .lake/build/core-correctness/arrayEraseIdxIfInBoundsMiddle.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayEraseIdxIfInBoundsMiddle .lake/build/core-correctness/arrayEraseIdxIfInBoundsMiddle.wat` returned `132`.
- [x] `node test/run_all.js` returned `checked 18 report classification cases`, `checked 263 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array swapIfInBounds

The extractor now lowers `Array.swapIfInBounds` for `Array UInt64`.  It evaluates the array and both indices once, returns the original array when either index is out of bounds, and otherwise allocates a fresh array, copies the cells, and writes both swapped elements from the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 19 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 266 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySwapIfInBoundsEnds --out .lake/build/core-correctness/arraySwapIfInBoundsEnds.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arraySwapIfInBoundsEnds .lake/build/core-correctness/arraySwapIfInBoundsEnds.wat` returned `4231`.
- [x] `node test/run_all.js` returned `checked 19 report classification cases`, `checked 266 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array reverse

The extractor now lowers `Array.reverse` for `Array UInt64`.  Arrays with length zero or one return the original pointer, matching the exposed Lean definition.  Longer arrays allocate a fresh array and copy source cells in reverse order.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 20 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 268 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayReverseRead --out .lake/build/core-correctness/arrayReverseRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayReverseRead .lake/build/core-correctness/arrayReverseRead.wat` returned `321`.
- [x] `node test/run_all.js` returned `checked 20 report classification cases`, `checked 268 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Proof-indexed Array updates

The extractor now lowers proof-indexed `Array.insertIdx`, `Array.eraseIdx`, and `Array.swap` for `Array UInt64`.  It erases proof arguments and reuses the existing in-bounds insert, erase, and swap operations.  The report now omits dependencies of expanded theorem declarations from the runtime frontier, so generated proof declarations do not introduce rejected external dependencies.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 21 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 271 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProofInsertIdxRead --out .lake/build/core-correctness/arrayProofInsertIdxRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayProofInsertIdxRead .lake/build/core-correctness/arrayProofInsertIdxRead.wat` returned `123`.
- [x] `node test/run_all.js` returned `checked 21 report classification cases`, `checked 271 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Identity function

The extractor now erases `id` for supported first-fragment values.  The scalar path covers ordinary identity applications, and the structured-value path preserves product laziness, so projecting one field of `id (bad, value)` does not force the unused field.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 22 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 273 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.idFunctionUInt64 --out .lake/build/core-correctness/idFunctionUInt64.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke idFunctionUInt64 .lake/build/core-correctness/idFunctionUInt64.wat 4` returned `5`.
- [x] `node test/run_all.js` returned `checked 22 report classification cases`, `checked 273 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Proof-indexed Array back

The extractor now lowers proof-indexed `Array.back` for `Array UInt64`.  It erases the nonempty proof and emits the same last-element read used by `Array.back!`; unlike `back!`, the demand analysis treats the proof-indexed form as nontrapping because Lean has checked the nonempty proof.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 23 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 274 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProofBackRead --out .lake/build/core-correctness/arrayProofBackRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayProofBackRead .lake/build/core-correctness/arrayProofBackRead.wat` returned `9`.
- [x] `node test/run_all.js` returned `checked 23 report classification cases`, `checked 274 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array insertIdx! and eraseIdx!

The extractor now lowers `Array.insertIdx!` and `Array.eraseIdx!` for `Array UInt64`.  Both operations bind the array and index once, branch on the bounds check, and use `trap` for the panic branch.  `Array.insertIdx!` keeps the inserted value inside the in-bounds branch, matching the exposed Lean definition.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 24 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 276 accepted, 21 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayInsertIdxBangRead --out .lake/build/core-correctness/arrayInsertIdxBangRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayInsertIdxBangRead .lake/build/core-correctness/arrayInsertIdxBangRead.wat` returned `123`.
- [x] `node test/run_all.js` returned `checked 24 report classification cases`, `checked 276 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array set variants

The extractor now lowers proof-indexed `Array.set` and total `Array.setIfInBounds` for `Array UInt64`.  `Array.set` erases the proof and uses the existing copy-on-write replacement path.  `Array.setIfInBounds` binds the array and index once, returns the original array when the index is out of bounds, and evaluates the replacement value only when the index is in bounds.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 25 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 279 accepted, 21 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySetIfInBoundsSkipsValueTrap --out .lake/build/core-correctness/arraySetIfInBoundsSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arraySetIfInBoundsSkipsValueTrap .lake/build/core-correctness/arraySetIfInBoundsSkipsValueTrap.wat` returned `7`.
- [x] `node test/run_all.js` returned `checked 25 report classification cases`, `checked 279 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Array swapAt

The extractor now lowers proof-indexed `Array.swapAt` for `Array UInt64`.  The operation erases its proof argument and returns an internal product whose first field reads the old element and whose second field is the copy-on-write updated array.  Lean 4.29 evaluates both the inline and let-bound `.1` projections without evaluating a replacement value that would panic, so the extractor preserves that product projection behavior.

Checks run:

- [x] `lake env lean /tmp/leanexe_swapAt_inline_check.lean` returned `2`.
- [x] `lake env lean /tmp/leanexe_swapAt_let_check.lean` returned `2`.
- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 26 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 282 accepted, 21 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySwapAtLetFirstSkipsValueTrap --out .lake/build/core-correctness/arraySwapAtLetFirstSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arraySwapAtLetFirstSkipsValueTrap .lake/build/core-correctness/arraySwapAtLetFirstSkipsValueTrap.wat` returned `2`.
- [x] `node test/run_all.js` returned `checked 26 report classification cases`, `checked 282 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Array map

The extractor now lowers `Array.map` for `Array UInt64` when the mapping function is a one-argument lambda returning `UInt64`.  The IR keeps a dedicated array-map expression with an explicit item slot for the mapped element.  CoreWasm evaluates the source array once, allocates a fresh result array with the same length, loads each source cell in index order, evaluates the mapper body with that cell bound to the item slot, and stores the mapped value into the result.  Empty arrays return an empty result without evaluating the mapper body.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 285 accepted, 21 rejected, and 7 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 27 report classification cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayMapEmptySkipsFunctionTrap --out .lake/build/core-correctness/arrayMapEmptySkipsFunctionTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayMapEmptySkipsFunctionTrap .lake/build/core-correctness/arrayMapEmptySkipsFunctionTrap.wat` returned `0`.
- [x] `node test/run_all.js` returned `checked 27 report classification cases`, `checked 285 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Structure result ABI design

The next implementation area is user-defined structures and returned structure values.  Lean 4.29 exposes the structure metadata needed for this through `Lean/Structure.lean`: `StructureInfo`, `getStructureInfo?`, `getStructureFieldsFlattened`, projection-function metadata, and `isStructureLike`.  The design in `spec.md` now fixes the direction before implementation: preserve source structure identity in the extractor, use Lean's flattened field order for layout, and flatten supported public fields to Wasm multi-value results at the ABI boundary.

Planned implementation sequence:

- [x] Add a structure-aware type form that records the source structure name and ordered runtime fields.
- [x] Extract constructor applications, projections, and structure update elaborations through that field representation.
- [x] Replace the single-result function ABI with a shared flattening path for public returns.
- [x] Emit Wasm function result vectors for flattened structure returns.
- [x] Add correctness cases for a returned scalar structure, nested structure fields, field projection laziness, and array fields in returned structures.
- [x] Add proof-field erasure and single-constructor structure matcher extraction after the extractor has explicit rules for proposition fields and recursor argument layout.

## 2026-05-08: User structures and multi-result returns

The extractor now has source-identified structure values through `Ty.struct` and an extractor-level structure value that records the Lean structure name and ordered fields.  The implemented slice accepts monomorphic, nonrecursive structures with supported runtime fields, lowers constructor applications and projection functions through Lean metadata, preserves lazy projection behavior for unused fields, and flattens exported structure results to Wasm multi-value result vectors.  The implementation deliberately leaves proof-field erasure, polymorphic structures, recursive structures, inherited-field flattening, structure entry parameters, and structure recursor matching unsupported until those cases have explicit rules.

The correctness examples now cover field projection laziness, structure update syntax, a nonrecursive helper returning a structure, direct structure returns, branch-selected structure returns, nested structure returns, and a returned structure that contains an `Array UInt64` field.  The JavaScript harness compares multi-value Wasm returns and validates array-field results by reading the returned array pointer in exported memory rather than asserting a specific allocation address.  A direct WAT check for `structureReturn` shows `(result i64 i64)`, and Wasmtime returns `5` and `6` for input `4`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 28 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 293 accepted, 22 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.structureReturn --out .lake/build/core-correctness/structureReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke structureReturn .lake/build/core-correctness/structureReturn.wat 4` returned `5` and `6`.
- [x] `node test/run_all.js` returned `checked 28 report classification cases`, `checked 293 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Structure matchers and proof fields

The structure extractor now classifies each constructor field as either a runtime field or an erased proof field.  The proof test handles direct `Prop` fields and fully applied constants whose declared result is `Prop`, which covers ordinary equality proofs such as `ok : value = value` without requiring runtime representation.  Runtime field indices now map from Lean source field indices to compact runtime indices, so projections and matcher binders skip erased fields while preserving source field order for the fields that remain.

Single-constructor structure matching now lowers through the same field representation as projections.  Direct structure recursors and generated matchers bind every source field in the arm; proof binders receive an erased placeholder, while runtime binders receive lazy field values.  This keeps `match ({ x := good, y := bad } : Point) with | { x, y := _ } => x` from emitting the unused `y` expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 29 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 299 accepted, 22 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 29 report classification cases`, `checked 299 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: User inductive values

The extractor now accepts monomorphic, nonrecursive user-defined inductives that are not structures and have no indices or type parameters.  `Ty.variant` records the source inductive name and constructor payload types, and the extracted value records the source name, tag expression, and payload values for every constructor.  Constructor applications erase proof fields and fill inactive constructor payloads with default values.  Generated matchers and direct recursors bind source fields in constructor order; erased proof fields receive the existing zero placeholder, while runtime fields remain lazy payload values.

Exported user-inductive results now use a fixed tagged ABI: tag first, followed by flattened payload slots for each constructor in declaration order.  A nullary enum returns one `i64` tag.  A two-constructor status type with one `UInt64` payload in each constructor returns three `i64` values: tag, first-constructor payload, and second-constructor payload.  Entry parameters for user inductives remain rejected until the public input ABI has structured tagged input rules.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.statusBranchReturn --out .lake/build/core-correctness/statusBranchReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke statusBranchReturn .lake/build/core-correctness/statusBranchReturn.wat 0` returned `0`, `5`, and `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke statusBranchReturn .lake/build/core-correctness/statusBranchReturn.wat 1` returned `1`, `0`, and `9`.
- [x] `node test/report_classification.js` returned `checked 31 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 312 accepted, 23 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 31 report classification cases`, `checked 312 accepted, 23 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Source-identified Except

`Except` now uses the `Ty.variant` path internally instead of the previous anonymous `sum` shape.  This separates `Except Unit α` from `Option α`, removing the old ambiguity where both types looked like `Unit ⊕ α` inside the extractor.  The public ABI still rejects `Except` parameters and results; this change only affects internal values, helper parameters, helper results, pattern matching, mapping, binding, conversion to `Option`, tag tests, and fallback.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 31 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 315 accepted, 22 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 31 report classification cases`, `checked 315 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Source-identified Option

`Option` now uses the same `Ty.variant` and `ExtractedValue.variant` path as user-defined inductives and `Except`.  The extractor removed the dedicated `ExtractedValue.option` case.  `none` is represented by tag `0` with no constructor fields, and `some` is represented by tag `1` with one payload field.  Public `Option` parameters and results remain rejected until the public tagged ABI admits them.

This completes the internal representation part of the unified sum work for built-in `Option` and `Except`.  Remaining ABI work must decide how hosts pass and receive tagged values, including inactive payload slots and flattening order, before those values can cross exported function boundaries.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 31 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 315 accepted, 22 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 31 report classification cases`, `checked 315 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Option and Except result ABI

Exported `Option` and `Except` results now use the same tagged multi-value ABI as source-defined inductive results.  `Option α` returns the tag followed by flattened payload slots for the `some` constructor.  `Except ε α` returns the tag, flattened error payload slots, and flattened success payload slots.  Inactive payload slots use the default values already used by source-defined inductive results.

The implementation keeps `Option` and `Except` entry parameters rejected.  Result support only relies on the existing output flattener; input support still needs source-order decoding rules for tagged parameter slots.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.optionReturn --out .lake/build/core-correctness/optionReturn.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.exceptPointReturn --out .lake/build/core-correctness/exceptPointReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke optionReturn .lake/build/core-correctness/optionReturn.wat 0` returned `0` and `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke optionReturn .lake/build/core-correctness/optionReturn.wat 3` returned `1` and `7`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke exceptPointReturn .lake/build/core-correctness/exceptPointReturn.wat 0` returned `0`, `7`, `0`, and `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke exceptPointReturn .lake/build/core-correctness/exceptPointReturn.wat 5` returned `1`, `0`, `5`, and `6`.
- [x] `node test/report_classification.js` returned `checked 33 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 323 accepted, 20 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 33 report classification cases`, `checked 323 accepted, 20 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Structured entry parameters

Entry parameter support now recurses through supported structures and tagged values.  Structure parameters flatten runtime fields in Lean field order after proof-field erasure.  Tagged parameters use the same slot order as tagged results: tag first, followed by each constructor's flattened payload slots in declaration order.  This admits monomorphic nonrecursive structure parameters, user-inductive parameters, `Option` parameters, and `Except` parameters when their runtime fields fit the current ABI.

The implementation reuses the existing `sourceParamBindings` path, which already reconstructed structured extractor values from flattened parameter slots.  The code change is therefore the signature gate, plus report classification for local user-inductive `casesOn` helpers generated by pattern matching on public tagged parameters.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.structureParam --out .lake/build/core-correctness/structureParam.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.statusParam --out .lake/build/core-correctness/statusParam.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.optionPointParam --out .lake/build/core-correctness/optionPointParam.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.exceptParam --out .lake/build/core-correctness/exceptParam.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke structureParam .lake/build/core-correctness/structureParam.wat 2 3` returned `23`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke statusParam .lake/build/core-correctness/statusParam.wat 0 5 0` returned `15`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke optionPointParam .lake/build/core-correctness/optionPointParam.wat 1 3 4` returned `7`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke exceptParam .lake/build/core-correctness/exceptParam.wat 1 0 5` returned `5`.
- [x] `node test/report_classification.js` returned `checked 38 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 333 accepted, 16 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 38 report classification cases`, `checked 333 accepted, 16 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Scalar array element types

The array representation now admits every element type that fits the existing one-cell array layout: `Bool`, `UInt8`, `UInt32`, `UInt64`, and bounded `Nat`.  Each element still occupies one eight-byte cell in linear memory.  `UInt8` and `UInt32` keep their constrained scalar representations inside that cell, `Bool` uses `0` or `1`, and `Nat` uses the bounded runtime representation.  This preserves the existing copy-on-write array operations without changing indexing, copying, or returned-pointer behavior.

Arrays of structures and tagged values remain planned.  They need a multi-slot element layout before implementation: element width, copy loops, field access, inactive payload slots, and host decoding must be specified together.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 42 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 339 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayUInt8Read --out .lake/build/core-correctness/arrayUInt8Read.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayUInt8Read .lake/build/core-correctness/arrayUInt8Read.wat` returned `1044`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayUInt32MapRead --out .lake/build/core-correctness/arrayUInt32MapRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayUInt32MapRead .lake/build/core-correctness/arrayUInt32MapRead.wat` returned `3`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayBoolRead --out .lake/build/core-correctness/arrayBoolRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayBoolRead .lake/build/core-correctness/arrayBoolRead.wat` returned `1`.
- [x] `node test/run_all.js` returned `checked 42 report classification cases`, `checked 339 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Fixed-width structure and tagged arrays

The IR and Wasm emitters now have explicit fixed-width array operations: allocation with an element width, slot-addressed reads, and slot-wise copy-on-write replacement.  The linear-memory layout keeps the length header at offset `0`.  Slot `s` of element `i` lives at cell index `1 + i * width + s`.  Scalar arrays are the width-one case.  Structure arrays flatten runtime fields in Lean field order after proof erasure.  Tagged arrays store the tag first, followed by every constructor payload slot in declaration order, matching the public tagged ABI.

The extractor now accepts fixed-width structure and tagged array literals, empty constructors, singleton construction, indexed reads, safe indexed reads, `back`, `back!`, `back?`, `set`, `set!`, `setIfInBounds`, `swapAt`, and returned pointers.  The older scalar-only copy operations now reject multi-slot arrays instead of compiling through one-cell loops.  Multi-slot `replicate`, `push`, `pop`, `append`, `extract`, insertion, erasure, swapping, reversal, modification, and mapping remain planned.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 46 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 345 accepted, 18 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureLiteralRead --out .lake/build/core-correctness/arrayStructureLiteralRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureLiteralRead .lake/build/core-correctness/arrayStructureLiteralRead.wat` returned `1234`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusLiteralMatch --out .lake/build/core-correctness/arrayStatusLiteralMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusLiteralMatch .lake/build/core-correctness/arrayStatusLiteralMatch.wat` returned `57`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.structurePointArrayReturn --out .lake/build/core-correctness/structurePointArrayReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke structurePointArrayReturn .lake/build/core-correctness/structurePointArrayReturn.wat` returned `4176` and `2`.
- [x] `node test/run_all.js` returned `checked 46 report classification cases`, `checked 345 accepted, 18 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array push, pop, append, and extract

Fixed-width arrays now lower `push`, `pop`, `append`, and `extract` for structure and tagged elements.  The IR records the element width for each operation.  The emitters allocate by payload-cell count rather than element count: `push` copies the original payload cells and writes the new element slots, `pop` copies all but the final element, `append` copies the left cells followed by the right cells, and `extract` converts the requested element range into source and destination cell offsets.

The extractor routes these operations through the multi-slot path whenever the element type has a fixed width.  Scalar arrays still use the existing one-cell operations.  Multi-slot `replicate`, `getD`, insertion, erasure, swapping, reversal, modification, and mapping remain planned.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 48 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 349 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureAppendRead --out .lake/build/core-correctness/arrayStructureAppendRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureAppendRead .lake/build/core-correctness/arrayStructureAppendRead.wat` returned `1234`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureExtractRead --out .lake/build/core-correctness/arrayStructureExtractRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureExtractRead .lake/build/core-correctness/arrayStructureExtractRead.wat` returned `3456`.
- [x] `node test/run_all.js` returned `checked 48 report classification cases`, `checked 349 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array insertion, erasure, swap, and reverse

Fixed-width arrays now lower bounded insertion, bounded erasure, bounded swaps, and reversal for structure and tagged elements.  The new IR nodes record element width, and the emitters copy by payload-cell offset.  Insertion copies the prefix, writes the flattened inserted value, and copies the suffix after the inserted element.  Erasure copies the prefix and shifts the suffix left by one element.  Swap copies the full payload and rewrites each selected element slot from the original array.  Reverse iterates by element index so slot order inside each element stays unchanged.

This completes the straightforward fixed-width copy operations for structure and tagged arrays.  Multi-slot `replicate`, `getD`, `modify`, and `map` remain planned because each needs an additional value-evaluation rule rather than only a copy-loop generalization.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 51 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 356 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureReverseRead --out .lake/build/core-correctness/arrayStructureReverseRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureReverseRead .lake/build/core-correctness/arrayStructureReverseRead.wat` returned `563412`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusReverseMatch --out .lake/build/core-correctness/arrayStatusReverseMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusReverseMatch .lake/build/core-correctness/arrayStatusReverseMatch.wat` returned `1175`.
- [x] `node test/run_all.js` returned `checked 51 report classification cases`, `checked 356 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array getD and modify

Fixed-width arrays now lower `Array.getD` and `Array.modify` for structure and tagged elements.  `Array.getD` is handled in the structured-value extractor, so the default value is selected field-by-field only when the index is out of bounds.  `Array.modify` loads the old element as a structured value, passes it to the source lambda, flattens the returned value, and lowers the update through the fixed-width copy-on-write replacement operation.

The remaining fixed-width array gaps are `Array.replicate` and `Array.map`.  Both need explicit value-evaluation rules in addition to slot copying: replication should evaluate the source value once and copy its flattened slots into each element, while mapping must define the result element layout and bind a structured source element in each loop iteration.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 54 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 361 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureGetDSkipsDefaultTrap --out .lake/build/core-correctness/arrayStructureGetDSkipsDefaultTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureGetDSkipsDefaultTrap .lake/build/core-correctness/arrayStructureGetDSkipsDefaultTrap.wat` returned `12`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusModifyMatch --out .lake/build/core-correctness/arrayStatusModifyMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusModifyMatch .lake/build/core-correctness/arrayStatusModifyMatch.wat` returned `107`.
- [x] `node test/run_all.js` returned `checked 54 report classification cases`, `checked 361 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array replicate

Fixed-width arrays now lower `Array.replicate` for structure and tagged elements.  The lowering evaluates the length and element value once, stores the flattened element slots in locals, allocates `length * width` payload cells, and writes the stored slots into each element position.  This keeps replication aligned with the fixed-width memory layout used by literals and copy-on-write updates.

The remaining fixed-width array gap is `Array.map`.  It needs the mapper body to receive a structured source element inside the loop and the result array to use the mapped element type's width, which is a distinct lowering from scalar `Array.map`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 56 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 363 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureReplicateRead --out .lake/build/core-correctness/arrayStructureReplicateRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureReplicateRead .lake/build/core-correctness/arrayStructureReplicateRead.wat` returned `1212`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusReplicateMatch --out .lake/build/core-correctness/arrayStatusReplicateMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusReplicateMatch .lake/build/core-correctness/arrayStatusReplicateMatch.wat` returned `1077`.
- [x] `node test/run_all.js` returned `checked 56 report classification cases`, `checked 363 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array map

Fixed-width arrays now lower `Array.map` for structure and tagged elements.  The IR records the source element width, result element width, source slot-local start, and flattened result expressions.  The emitters load each source element into local slots, evaluate the mapper body against that structured value, and store the flattened result slots into a freshly allocated result array.

This completes the planned fixed-width array operation set for monomorphic nonrecursive structures and small tagged values.  Nested arrays, polymorphic arrays, recursive element types, and owned byte-array results remain outside this slice.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 58 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 366 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureMapRead --out .lake/build/core-correctness/arrayStructureMapRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureMapRead .lake/build/core-correctness/arrayStructureMapRead.wat` returned `3375`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusMapMatch --out .lake/build/core-correctness/arrayStatusMapMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusMapMatch .lake/build/core-correctness/arrayStatusMapMatch.wat` returned `1168`.
- [x] `node test/run_all.js` returned `checked 58 report classification cases`, `checked 366 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Structured Nat-fuel recursion results

The Nat-fuel recursion extractor now handles supported structured result values.  Base and early-exit arms lower through `extractValueFrom`, the final loop result uses structured `valueIte` when the recursion has an early-exit arm, and the exported function result flattens through the normal ABI path.  This admits recursive functions returning structures, user-defined tagged values, `Option`, or `Except` when the result fields fit the current ABI.

This does not broaden the accepted recursive call shape.  The successor arm still must tail-call the same recursive handle directly or place that tail call in one branch of the immediate `if`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 60 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 369 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recPointFuel --out .lake/build/core-correctness/recPointFuel.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke recPointFuel .lake/build/core-correctness/recPointFuel.wat 2 5` returned `7` and `8`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recStatusExitFuel --out .lake/build/core-correctness/recStatusExitFuel.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke recStatusExitFuel .lake/build/core-correctness/recStatusExitFuel.wat 10 1` returned `1`, `0`, and `3`.
- [x] `node test/run_all.js` returned `checked 60 report classification cases`, `checked 369 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Structured Nat-fuel recursion state

The existing Nat-fuel recursion path already flattened structured carried parameters through the same ABI machinery used for ordinary calls.  The new tests make that support explicit for a carried structure and a carried tagged value.  The loop update assigns each flattened carried slot through temporary locals, so multi-slot carried values update atomically with respect to later slot assignments in the same recursive step.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 62 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 372 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recPointCarryFuel --out .lake/build/core-correctness/recPointCarryFuel.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke recPointCarryFuel .lake/build/core-correctness/recPointCarryFuel.wat 3 1 10` returned `4` and `16`.
- [x] `node test/run_all.js` returned `checked 62 report classification cases`, `checked 372 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray results and push

The generic compiler now accepts `ByteArray` results through the same pointer-length ABI used for `ByteArray` parameters.  Returned buffers may alias input memory or slices, or they may point to arena memory allocated by compiled code.  Hosts must read returned bytes before calling `reset`, because the arena owns the allocation lifetime and the compiler does not free individual byte buffers.

`ByteArray.empty` lowers to `(0, 0)`.  `ByteArray.push` evaluates the source and pushed byte, allocates `len + 1` bytes, copies the source bytes with byte loads and stores, and writes the appended byte.  The scalar length expression still forces the pushed value, so a trap in the byte expression is preserved even when source code asks only for the size of the pushed array.  `LeanExe.Examples.ByteArrayPrograms.tailSlice` covers a returned view into input memory rather than an owned arena allocation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 42 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 374 accepted, 16 rejected, and 8 trapped cases`.
- [x] `.lake/build/bin/lean-wasm report --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.appendBang` reported `entry shape: ByteArray -> ByteArray`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke bytesABC .lake/build/bytearray-programs/bytesABC.wasm` returned pointer `4099` and length `3`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/appendBang.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 64 report classification cases`, `checked 374 accepted, 16 rejected, and 8 trapped cases`, `checked 42 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray append

The generic compiler now lowers `ByteArray.append` through a second byte-buffer allocation primitive.  The emitted code evaluates both inputs, allocates `left.size + right.size` bytes, copies the left bytes into the result, copies the right bytes after them, and returns the result pointer.  The length expression evaluates both operands, so a trap hidden in the construction of the right operand is still observed when source code asks only for the appended buffer's size.

`LeanExe.Examples.ByteArrayPrograms.appendABCXYZ` covers appending two compiler-constructed buffers.  `appendInputABC` covers appending a compiler-constructed suffix to host-provided input.  The memory harness reads the returned pointer-length pair and compares the result bytes.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 45 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 376 accepted, 16 rejected, and 9 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 66 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke appendABCXYZ .lake/build/bytearray-programs/appendABCXYZ.wasm` returned pointer `4108` and length `6`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/appendInputABC.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 66 report classification cases`, `checked 376 accepted, 16 rejected, and 9 trapped cases`, `checked 45 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray set

The generic compiler now lowers proof-indexed `ByteArray.set`.  The emitted code evaluates the source, index, and replacement byte, checks the index before writing, allocates a fresh buffer with the original length, copies the source bytes, writes the replacement byte at the requested index, and returns the result pointer.  The length expression forces the index and replacement byte, so traps in those demanded expressions are preserved when source code asks only for the updated buffer's size.

`LeanExe.Examples.ByteArrayPrograms.setABC` covers a compiler-constructed buffer.  `setFirstBang` covers a host-provided input buffer and the empty-input branch where the proof-indexed update is not evaluated.  The operation remains proof-indexed; unchecked byte updates still need a separate source form and trap policy.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 49 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 378 accepted, 16 rejected, and 10 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 68 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke setABC .lake/build/bytearray-programs/setABC.wasm` returned pointer `4102` and length `3`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/setFirstBang.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 68 report classification cases`, `checked 378 accepted, 16 rejected, and 10 trapped cases`, `checked 49 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray mk

The generic compiler now lowers `ByteArray.mk` for `Array UInt8`.  The emitted code evaluates the source array, reads its length header, allocates that many bytes, copies each `UInt8` cell into one byte of the new buffer, and returns the result pointer.  This gives byte literals a direct source form through `ByteArray.mk #[(65 : UInt8), ...]` rather than requiring a chain of `push` calls.

`LeanExe.Examples.ByteArrayPrograms.mkABC` covers the source form used by ordinary byte literals.  `LeanExe.Examples.Correctness.byteArrayMkSizeForcesArrayTrap` checks that asking for the size of the constructed byte array still evaluates the source array element.  The current support is monomorphic: the source array must be `Array UInt8`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 50 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 380 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 69 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke mkABC .lake/build/bytearray-programs/mkABC.wasm` returned pointer `4224` and length `3`.
- [x] `node test/run_all.js` returned `checked 69 report classification cases`, `checked 380 accepted, 16 rejected, and 11 trapped cases`, `checked 50 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray foldl

The generic compiler now lowers `ByteArray.foldl` for one-slot scalar accumulators.  The emitted code evaluates the buffer, start, stop, and initial accumulator, clamps stop to the buffer size, skips the body when the range is empty, and otherwise loops over bytes from left to right.  Each iteration loads one `UInt8`, evaluates the fold function body against the current accumulator and byte, stores the new accumulator, and advances the index.

`LeanExe.Examples.ByteArrayPrograms.foldSum` covers a full-buffer fold, and `foldWindowDecimal` covers an explicit start and stop range.  `LeanExe.Examples.Correctness.byteArrayFoldEmptySkipsFunctionTrap` checks that an empty range does not evaluate the fold body.  This adds a loop-like source form for byte processing without relying on the restricted Nat-fuel recursion pattern.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 56 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 383 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 70 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/foldWindowDecimal.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 70 report classification cases`, `checked 383 accepted, 16 rejected, and 11 trapped cases`, `checked 56 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray copySlice

The generic compiler now lowers value-level `ByteArray.copySlice`.  The implementation follows the Lean 4.29.1 definition in `Init/Data/ByteArray/Basic.lean`: it copies the destination prefix, a bounded source slice, and the destination suffix beginning after the bytes actually copied.  The `exact` argument affects capacity behavior in the runtime primitive, but the pure Lean definition does not use it to determine the resulting bytes, so extraction does not evaluate it.

`LeanExe.Examples.ByteArrayPrograms.copyInputMiddle` covers replacement inside an existing destination.  `copyInputPastDest` covers the case where `destOff` is beyond the destination size; the result appends the available source bytes without inserting padding.  `copyShortSource` checks that the suffix starts after the bytes copied, not after the requested length.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 63 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 387 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 71 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/copyInputPastDest.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 71 report classification cases`, `checked 387 accepted, 16 rejected, and 11 trapped cases`, `checked 63 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array foldl

The generic compiler now lowers `Array.foldl` for fixed-width arrays and one-slot accumulators.  This covers scalar arrays and arrays whose elements flatten to a fixed number of scalar slots, including monomorphic nonrecursive structures and small tagged values.  The emitted code evaluates the array, start, stop, and initial accumulator, clamps stop to the array size, loads each element into local slots, evaluates the fold body against the accumulator and current element, and stores the new accumulator.

`LeanExe.Examples.Correctness.arrayFoldSum` and `arrayFoldWindow` cover scalar arrays, including an explicit start and stop range.  `arrayFoldEmptySkipsFunctionTrap` checks that an empty range does not evaluate the fold body.  `arrayStructureFoldRead` covers a structured element loaded from a multi-slot array layout.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 391 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 72 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayStructureFoldRead.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 72 report classification cases`, `checked 391 accepted, 16 rejected, and 11 trapped cases`, `checked 63 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray append notation

The extractor now lowers `HAppend.hAppend` when the checked result type is `ByteArray`.  The lowering reuses the same allocation and copy operation as `ByteArray.append`: it evaluates the left and right operands, allocates the combined byte length, copies the left bytes first, and copies the right bytes after them.  Non-`ByteArray` `HAppend.hAppend` applications still pass through the existing scalar extraction path, which preserves the prior array append-notation support.

`LeanExe.Examples.ByteArrayPrograms.appendNotationABCXYZ` covers ordinary `++` source syntax over byte arrays.  The report now classifies `HAppend.hAppend` as implemented for supported array and byte-array append notation.  The generated WAT for the new example validates under the local Wasmtime tool.

Checks run:

- [x] `lake build`
- [x] `node test/bytearray_alloc.js` returned `checked 64 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 391 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 73 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/appendNotationABCXYZ.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 73 report classification cases`, `checked 391 accepted, 16 rejected, and 11 trapped cases`, `checked 64 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray set!

The generic compiler now lowers trapping `ByteArray.set!`.  The operation uses the existing copy-on-write byte update lowering: it evaluates the source, index, and replacement byte, checks the index, allocates a fresh buffer with the original length, copies the source bytes, writes the replacement byte, and traps when the index is out of bounds.  This gives source code the ordinary non-proof update form while keeping alias behavior conservative.

`LeanExe.Examples.ByteArrayPrograms.setBangABC` covers a compiler-constructed buffer, and `setBangFirstQuestion` covers a host-provided buffer guarded by an empty check.  `LeanExe.Examples.Correctness.byteArraySetBangTrap` checks the out-of-bounds trap path.  The implementation does not add `USize` indexing or `ByteArray.uset`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 68 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 392 accepted, 16 rejected, and 12 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 74 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/setBangFirstQuestion.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 74 report classification cases`, `checked 392 accepted, 16 rejected, and 12 trapped cases`, `checked 68 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray UInt64 decoding

The generic compiler now lowers `ByteArray.toUInt64LE!` and `ByteArray.toUInt64BE!` from Lean's `Init.Data.ByteArray.Extra` module.  The lowering checks that the byte-array length is exactly eight, then emits byte loads, left shifts, and bitwise-or operations to construct the `UInt64` result.  A wrong length traps in Wasm instead of calling Lean's panic runtime.

`LeanExe.Examples.ByteArrayPrograms.readUInt64LE` and `readUInt64BE` cover host-provided byte input.  `LeanExe.Examples.Correctness.byteArrayToUInt64LE` and `byteArrayToUInt64BE` cover compiler-constructed byte arrays, while `byteArrayToUInt64Trap` covers the size-check failure.  This adds a common binary-parser primitive without adding string or `IO` support.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 394 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 75 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/readUInt64LE.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 75 report classification cases`, `checked 394 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray findIdx?

The generic compiler now lowers `ByteArray.findIdx?` for direct one-argument byte predicates returning `Bool`.  The emitted search scans bytes from left to right, returns `some index` at the first true predicate result, and returns `none` if the search reaches the end.  Empty search ranges do not evaluate the predicate.

`LeanExe.Examples.ByteArrayPrograms.findQuestion` and `findQuestionAfterFirst` cover host-provided byte input.  `LeanExe.Examples.Correctness.byteArrayFindIdxSome`, `byteArrayFindIdxNone`, `byteArrayFindIdxStart`, and `byteArrayFindIdxEmptySkipsPredicateTrap` cover returned `Option Nat` values and skipped predicate evaluation.  The current support requires the predicate to remain a direct lambda after elaboration; general closure values remain outside the subset.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 398 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 76 report classification cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/byteArrayFindIdxStart.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 76 report classification cases`, `checked 398 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array findIdx?

The generic compiler now lowers `Array.findIdx?` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The emitted search loads each element into the same local slot representation used by `Array.map` and `Array.foldl`, checks the predicate, returns `some index` at the first true result, and returns `none` at the end of the array.  Empty arrays do not evaluate the predicate.

`LeanExe.Examples.Correctness.arrayFindIdxSome` and `arrayFindIdxNone` cover scalar arrays.  `arrayFindIdxStructure` covers a structure-array element, and `arrayFindIdxStatus` covers a tagged element with a predicate that matches on the source-defined inductive.  `arrayFindIdxEmptySkipsPredicateTrap` checks skipped predicate evaluation.  The current support requires a direct lambda predicate and does not compile escaped predicate values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 403 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 77 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayFindIdxStatus.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 77 report classification cases`, `checked 403 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array any and all

The generic compiler now lowers `Array.any` and `Array.all` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The lowering clamps `stop` to the array size, starts at `start`, and short-circuits on the first decisive result.  Empty ranges return `false` for `any` and `true` for `all` without evaluating the predicate.

`LeanExe.Examples.Correctness.arrayAnySome`, `arrayAnyWindowFalse`, `arrayAllScalars`, and `arrayAllWindowTrue` cover scalar arrays and explicit ranges.  `arrayAllStructure` covers structure elements, and `arrayAnyStatus` covers tagged elements with a predicate that matches on a source-defined inductive.  `arrayAnyEmptySkipsPredicateTrap` and `arrayAllEmptySkipsPredicateTrap` check skipped predicate evaluation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 411 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 78 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayAllStructure.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 78 report classification cases`, `checked 411 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array find?

The generic compiler now lowers `Array.find?` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The operation returns a source-shaped `Option` payload, so scalar, structure, and tagged elements all use the existing `Option` ABI and internal representation.  The current lowering emits one search for the tag and one search for each demanded payload slot; this preserves pure results but should be replaced by a shared loop result before treating `find?` as a performance primitive.

`LeanExe.Examples.Correctness.arrayFindSome` and `arrayFindNone` cover scalar payloads.  `arrayFindStructure` covers a returned structure payload, and `arrayFindStatus` covers a returned tagged payload.  `arrayFindEmptySkipsPredicateTrap` checks skipped predicate evaluation on an empty array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 416 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 79 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayFindStatus.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 79 report classification cases`, `checked 416 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array filter

The generic compiler now lowers `Array.filter` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The emitted code clamps `stop` to the source size, scans the selected range from left to right, copies matching element slots into a new arena array, and writes the matched count into the result header.  The arena reservation uses the source length as capacity, so the allocated region can exceed the observable result length.

`LeanExe.Examples.Correctness.arrayFilterScalarsRead`, `arrayFilterWindowRead`, and `arrayFilterNoneSize` cover scalar arrays, explicit ranges, and empty results.  `arrayFilterStructureRead` covers filtered structure elements, and `arrayFilterStatusRead` covers filtered tagged elements.  `arrayFilterEmptySkipsPredicateTrap` checks skipped predicate evaluation for an empty source.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 422 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 80 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayFilterStructureRead.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 80 report classification cases`, `checked 422 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Internal recursive inductives

The extractor now accepts monomorphic self-recursive user-defined inductives as internal values.  `Ty.recVariant` marks a recursive source type, and `ExtractedValue.recursiveVariant` keeps freshly constructed values lazy until a pointer is required.  When the value crosses a strict boundary, the extractor materializes it into the arena as a fixed-slot object: slot `0` stores the constructor tag, and later slots store flattened payloads for every constructor in declaration order.  Recursive fields store one pointer slot.  Matches over materialized values load the tag and demanded fields from the object, while matches over fresh constructor values use the existing lazy payload path.

`LeanExe.Examples.Correctness.U64List` covers construction, nested matching, branch-selected recursive values, and a fuel-recursive traversal that carries the list pointer through the existing `Nat`-fuel loop form.  Public recursive values remain outside the Wasm ABI: `rejectRecursiveInductiveParam` and `rejectRecursiveInductiveReturn` check that entry parameters and results of recursive inductive type are rejected.  The implementation does not handle mutual recursion, polymorphic recursive types, arrays of recursive values, recursive structures, or a garbage collector.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 429 accepted, 18 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 80 report classification cases`, `checked 429 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ASCII string library

`LeanExe.AsciiString` is a one-field structure over `ByteArray`, with explicit checked and trusted constructors.  The checked path uses a fuel-recursive byte scan and returns `Option AsciiString`; the trusted path wraps a byte buffer without validation.  The representation keeps the WASM ABI unchanged, because an ASCII string flattens to the pointer-length pair of its `ByteArray` field.

`LeanExe.Examples.AsciiStringPrograms` covers ASCII validation, checked conversion, checked byte push, trusted append, extraction, and returned byte output.  The test harness compiles those examples through the generic compiler and compares WASM results with expected bytes.  The current library intentionally avoids Lean `String` and Unicode semantics; it is byte-oriented text for parsers and generators that need ASCII syntax.

Checks run:

- [x] `lake build LeanExe.Examples.AsciiStringPrograms`
- [x] `node test/asciistring.js` returned `checked 14 asciistring cases`.
- [x] `node test/report_classification.js` returned `checked 85 report classification cases`.
- [x] `node test/run_all.js` returned `checked 85 report classification cases`, `checked 429 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, and `checked 56 cases`.

## 2026-05-11: Schema-specific JSON over ASCII

`LeanExe.Examples.JsonDouble.transform` is the first JSON-shaped example.  It accepts a `ByteArray`, validates it as `AsciiString`, parses the exact object shape `{ "n" : digits }`, doubles the parsed `UInt64` when the result fits, and returns generated JSON bytes.  It returns `{"error":1}` for malformed input, non-ASCII input, parse overflow, and doubled-value overflow.

The compiler change adds a value-level call binding for helper calls that return structured values.  A direct call now stores all flattened result slots in locals and reconstructs the source value shape, so callers can match an `Option` result or project a structure returned by a bounded recursive helper.  `recPointFuelCallRead` covers this path independently of the JSON example, and the JSON parser exercises an `Option ParsedNumber` result from a recursive decimal parser.

The JSON support remains deliberately schema-specific.  It has no general JSON AST, no string escape parser, no arrays, no object field search, and no Unicode handling.  Those belong in later library work once the accepted subset has enough text and recursive data support to make a general parser useful.

Checks run:

- [x] `lake build LeanExe.Examples.JsonDouble`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/json_double.js` returned `checked 12 json double cases`.
- [x] `node test/report_classification.js` returned `checked 87 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 430 accepted, 18 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 87 report classification cases`, `checked 430 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 12 json double cases`, and `checked 56 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-double/transform.wat` accepted the generated module.

## 2026-05-11: Reusable ASCII JSON helpers

The JSON examples now share small helper modules instead of carrying local byte parsers in each example.  `LeanExe.Ascii.Basic` contains byte constants, whitespace scanning, and byte expectations; `LeanExe.Ascii.Decimal` contains checked unsigned decimal parsing and rendering for `UInt64`; `LeanExe.Ascii.Json` contains one-byte field-name parsing and the shared `{"error":1}` result.  `JsonDouble` now uses those helpers, and `JsonAdd` demonstrates a fixed two-field object that returns a checked `UInt64` sum.

The compiler now emits a direct WASM call for a nonrecursive helper with a one-slot scalar result when demand analysis proves that strict argument evaluation preserves Lean behavior.  The first version allowed structured direct calls without enough proof, which forced inactive `Option` payloads across the flattened result ABI and made `AsciiString.getD` trap on out-of-bounds input.  Structured helper returns still work, but nonrecursive structured helpers remain inlined unless the current recursive call machinery or an accepted call shape requires flattened result slots.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 22 json program cases`.
- [x] `node test/report_classification.js` returned `checked 88 report classification cases`.
- [x] `node test/run_all.js` returned `checked 88 report classification cases`, `checked 430 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 22 json program cases`, and `checked 56 cases`.

## 2026-05-11: JSON Collatz length example

`LeanExe.Examples.JsonCollatzLength.transform` accepts a JSON-shaped `ByteArray` request of the form `{ "collatzLengthFor" : digits }` and returns `{"length":N}`.  The length counts terms, so `{"collatzLengthFor":41}` returns `{"length":110}`.  The program uses a checked Collatz length helper that rejects zero, decimal parse overflow, `3n+1` overflow under `UInt64`, and failure to reach `1` before the existing `maxSteps` fuel limit.

The JSON helper layer now has `expectBytes` and `expectFieldName` for fixed byte-string field names.  `expectBytesFuel` had to follow the accepted single-branch tail-recursive shape; an earlier nested-`if` loop was valid Lean but outside the current recursion recognizer.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 31 json program cases`.
- [x] `node test/report_classification.js` returned `checked 89 report classification cases`.
- [x] `node test/run_all.js` returned `checked 89 report classification cases`, `checked 430 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 31 json program cases`, and `checked 56 cases`.

## 2026-05-11: ASCII string literals for ByteArray

The extractor now lowers `String.toUTF8` when the receiver is a compile-time ASCII string literal.  The accepted source form is standard Lean syntax such as `"collatzLengthFor".toUTF8`, and the lowered value uses the same byte-buffer representation as `ByteArray.mk`.  Runtime `String` values remain unsupported: `String` parameters, `String` results, nonliteral receivers, non-ASCII literals, indexing, decoding, and general string operations are rejected.

The JSON examples now use string literals for fixed output prefixes and field names.  `LeanExe.Examples.Correctness.byteArrayStringLiteralReturn` and `byteArrayStringLiteralSize` cover accepted byte output and size queries, while `rejectRuntimeStringToUTF8` covers rejection of a nonliteral string receiver.

Checks run:

- [x] `lake build`
- [x] `node test/core_correctness.js` returned `checked 432 accepted, 19 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 31 json program cases`.
- [x] `node test/report_classification.js` returned `checked 89 report classification cases`.
- [x] `node test/run_all.js` returned `checked 89 report classification cases`, `checked 432 accepted, 19 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 31 json program cases`, and `checked 56 cases`.

## 2026-05-11: Internal arrays of recursive values

The compiler now treats a recursive inductive value as a one-slot array element when the array stays inside compiled Lean code.  The slot holds the heap pointer used for materialized recursive values.  This admits internal values such as `Array U64List` and recursive constructors that contain `Array U64Tree`.  Entry parameters and entry results whose array element layout contains a recursive value remain rejected.

The extractor changes stay narrow.  `arrayElementSlots?` now assigns one slot to `Ty.recVariant`, array element flattening materializes fresh recursive constructor values to heap pointers, and array load, find, and loop-local binding rebuild `ExtractedValue.heapVariant` from the stored pointer.  Recursive field type analysis now recognizes `Array self` structurally, avoiding recursive-layout rediscovery while checking constructors such as `U64Tree.node : Array U64Tree -> U64Tree`.  Direct helper calls now flatten arguments and non-exported results with the internal value flattener, so internal arrays of recursive values can pass through ordinary local helpers without becoming part of the public ABI.

`LeanExe.Examples.Correctness` covers recursive arrays through literals, `push`, `set!`, `map`, `foldl`, safe indexing, and a recursive inductive constructor that stores `Array U64Tree`.  The accepted cases exercise both fresh constructor values and recursive pointers loaded back from array storage.  The rejected cases cover public ABI rejection for `Array U64List` parameters and results.

Checks run:

- [x] `lake build`
- [x] `node test/core_correctness.js` returned `checked 437 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 90 report classification cases`.
- [x] `node test/run_all.js` returned `checked 90 report classification cases`, `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 31 json program cases`, and `checked 56 cases`.

## 2026-05-11: Limited JSON field tools

`LeanExe.Ascii.Json` now has reusable ASCII-only field lookup and object generation helpers.  `findFieldRange` scans a top-level object for a named field, and the typed getters read `UInt64`, restricted unescaped ASCII strings, booleans, null, nested object slices, nested array slices, or raw value slices from that range.  The value skipper handles unknown nested object and array values by tracking nesting depth and restricted strings, which supports practical field lookup without claiming full JSON grammar validation.

The generator side now has quoted-string helpers, field-prefix helpers, typed field appenders, and one-field object constructors for `UInt64`, `Bool`, and restricted ASCII strings.  The string grammar remains intentionally small: bytes must be ASCII, at least `32`, and neither quote nor backslash.  `appendRawField?` accepts a raw value only when the same limited value skipper consumes the whole slice after whitespace.

`LeanExe.Examples.JsonTools.transform` demonstrates byte-output generation through a direct one-field parse, and `LeanExe.Examples.JsonTools.lookup` demonstrates generic lookup across a skipped nested object as a scalar entry.  The split records a compiler limitation found during this work: a `ByteArray`-returning function that demands an `Option UInt64` payload found after a skipped field can trap in WASM even though the scalar lookup itself is correct.  That points at structured-value lowering around `Option` matches feeding byte-array output, not at the source JSON helper.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 45 json program cases`.
- [x] `node test/report_classification.js` returned `checked 92 report classification cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 45 json program cases`, and `checked 56 cases`.

## 2026-05-11: Collatz JSON output uses the helper layer

`LeanExe.Examples.JsonCollatzLength.resultJson` now emits its success object through `Ascii.Json.object1UInt64` instead of hand-building the prefix and appending the decimal digits.  The input parser remains the exact one-field parser.  Replacing that parser with `Ascii.Json.getUInt64Field` makes the generated byte-output function enormous under the current inlining strategy; the Node-based test harness refused to instantiate that function because of its per-function size.  The root cause is the compiler's handling of structured helper returns, so generic field lookup should wait for that compiler fix before it becomes the byte-output Collatz path.

## 2026-05-11: Structured helper calls and result materialization

The compiler now emits real WASM calls for accepted structured helper returns when strict argument evaluation is valid.  The IR has statement-level multi-result calls, so a helper returning `Option`, a structure, a tagged value, or a `ByteArray` stores its flattened result slots once before later projections or matches consume them.  The prior expression-only lowering copied a structured call into each demanded slot, which made the generic JSON Collatz example expand into hundreds of megabytes of WAT.

Conditional structured results now materialize through statement-level branches into result locals.  This preserves source-level branch selection for helpers that allocate or can trap, and it prevents a `ByteArray` result from calling the same branch once for the pointer and again for the length.  Safe array and byte-array indexing also guard inactive `Option` payloads, so a `none` result no longer performs the out-of-bounds payload read that Lean source code would skip.

`LeanExe.Examples.JsonCollatzLength.parseObject` now uses `Ascii.Json.getUInt64Field`, and the success output still uses `Ascii.Json.object1UInt64`.  The generated Collatz JSON module is `238332` bytes of WAT and `22735` bytes of WASM; the largest emitted function is `1580` WAT lines.  Wasmtime accepts the emitted WAT, and the full test suite reports `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 45 json program cases`, and `checked 56 cases`.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 45 json program cases`.
- [x] `node test/report_classification.js` returned `checked 92 report classification cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 45 json program cases`, and `checked 56 cases`.

## 2026-05-11: Strict structured materialization sites

Strict helper-call arguments now materialize top-level `let` and direct-call values before flattening argument slots.  The implementation binds each flattened argument slot to locals in source argument order before the call, so later structured helper arguments cannot run before earlier scalar expressions.  A structured helper result passed to another helper is therefore evaluated once, and recursive loop argument updates run any required structured calls before assigning carried slots.  The change keeps strict-call demand analysis in charge of whether a call may be emitted.

Eager fixed-width array element operations use the same materialization step for literal items, singleton values, pushed values, proof-indexed inserts and sets, and bang inserts and sets under their in-bounds branch.  For updates with array and index operands, the extractor binds those operands before running materialized element lets.  Guarded operations that define skipped-value behavior, including `setIfInBounds`, `insertIdxIfInBounds`, `modify`, `swapAt` projections, and `map` bodies, still keep value expressions inside the guarded or per-element expression.  Moving those expressions to an outer statement would force source expressions that Lean code can leave unevaluated.

`LeanExe.Examples.JsonTools.transform` now reads `n` through `Ascii.Json.getUInt64Field`, matching the scalar lookup example and accepting unknown skipped values before the requested field.  The JSON harness includes a one-megabyte WAT size guard for `JsonCollatzLength.transform`; the current generated WAT is `257071` bytes.  The core correctness corpus adds cases for structured helper results as call arguments, structured helper results stored as array elements, inactive structured safe-index payloads, and branch-selected `ByteArray` helper results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 442 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 46 json program cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 442 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-programs/JsonCollatzLength-transform.wat`

## 2026-05-11: Strict materialization regressions and size guards

The extractor now names the strict-boundary helpers as `StrictSlots`, `StrictArgs`, `materializeStrictInternalSlots`, and `materializeStrictArrayElementSlots`.  This keeps the statement-like path separate from lazy expression flattening.  `Array.replicate` now uses the strict array-element path too, binding the count expression before running materialized element lets.

The correctness corpus adds guarded helper regressions for `insertIdxIfInBounds`, `setIfInBounds`, and empty `map` over structured arrays.  Each case passes a helper whose payload traps if evaluated, so moving a structured value out of a skipped branch would fail.  `arrayStructureReplicateHelperRead` covers the strict eager replicate path, and `core_correctness.js` adds a WAT size guard for that example.

The JSON harness now guards `JsonTools.transform` as well as `JsonCollatzLength.transform`.  Current guarded WAT sizes are `257071` bytes for `JsonCollatzLength.transform`, `229962` bytes for `JsonTools.transform`, and `9468` bytes for `arrayStructureReplicateHelperRead`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 446 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 46 json program cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 446 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-programs/JsonCollatzLength-transform.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-programs/JsonTools-transform.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayStructureReplicateHelperRead.wat`

## 2026-05-11: Recursive step let bindings

The Nat-fuel recursion recognizer now accepts local `let` bindings at the start of the successor branch before the tail call or before the immediate `if` that selects between an early exit and the tail call.  This supports ordinary state-staging code such as computing the next accumulator value once, naming it, and then passing it to the next iteration or testing it for early exit.  The recognizer tracks the shifted recursive handle under each Lean `.letE`, so a recursive call under one or more lets still points at the generated `Nat.brecOn` handle rather than at the newest local binding.

Condition extraction now treats local `let` bindings as lazy condition-local bindings, matching value extraction and scalar expression extraction.  The prior path routed a let-bound proposition condition through scalar expression extraction, which rejected Lean's `Eq` proposition in a condition such as `let next := acc + 1; if next == 3 then ...`.  The corrected path preserves unused-let laziness: a step-local binding that would trap if evaluated remains skipped when the recursive step body does not demand it.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 449 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 449 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: List-shaped structural recursion

The extractor now lowers a narrow structural-recursion shape for supported self-recursive inductives.  The accepted helper has one parameter of the recursive inductive type, and each constructor may expose at most one direct self-recursive field.  The lowering recognizes Lean's generated `brecOn` form, matches on the heap tag, binds constructor fields from the heap object, and turns the generated `PProd.fst` below projection into a direct recursive WASM call on the recursive field.

This admitted ordinary list traversals without an explicit fuel parameter.  `LeanExe.Examples.Correctness.u64ListStructuralSum` summed `U64List` through direct structural recursion and was called from the public zero-argument demo.  At that checkpoint, `rejectStructuralBinarySize` used a binary recursive constructor with two direct recursive fields and was rejected with `structural recursion over multiple recursive fields is unsupported`; the later branching structural recursion entry supersedes that limitation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 450 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 450 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: Parser state fixture

`LeanExe.Examples.Correctness.DigitState` is a small parser-state structure with a byte cursor and `UInt64` accumulator.  `digitStateParseFuel` carries that state through the accepted Nat-fuel loop shape, uses a helper to test whether the current byte is an ASCII digit, and uses a helper to advance the cursor and add the digit value.  The examples cover an all-digit input and an input that stops at a non-digit byte.

This slice did not require a compiler change.  It records that the current subset already supports a common parser style: a `ByteArray` input, a cursor-state structure, helper calls for predicate and step logic, and a bounded state-passing loop.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 452 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 452 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: ASCII string comparison utilities

`AsciiString` now includes `equals`, `startsWith`, and `containsByte`.  The implementations use the accepted Nat-fuel tail-recursive loop shape with explicit accumulator state rather than nested recursive branches, so they compile through the current recursion recognizer.  The example module exposes these utilities through byte-array entry points that validate ASCII input before constructing `AsciiString` values.

Checks run:

- [x] `lake build LeanExe.Examples.AsciiStringPrograms`
- [x] `node test/asciistring.js` returned `checked 22 asciistring cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 452 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: Structure-backed integer map

`LeanExe.Examples.IntMap` now represents each hash-table cell as a `Slot` structure and the table as a `Table` structure over `Array Slot`.  The example still uses a fixed capacity of `256`, open addressing, key `0` as the empty marker, and keys `1` through `100` mapped to `k * 10 + 7`.  This updates the old raw adjacent-word array example to current subset style.

The new `test/intmap.js` regression compiles `checksum` and `query` and runs them under the checked-in Wasmtime binary.  It checks the aggregate checksum and lookups for the first inserted key, last inserted key, and a missing key.

Checks run:

- [x] `lake build LeanExe.Examples.IntMap`
- [x] `node test/intmap.js` returned `checked 4 intmap cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 452 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Pure for loops over bytes and arrays

The extractor now recognizes Lean's generated `ForIn.forIn` form when the monad is `Id`, the collection is `ByteArray` or a fixed-width `Array`, and the accumulator has a supported one-slot type.  The lowering extracts the yielded accumulator from a `ForInStep.yield` body and emits the existing byte-array or array fold IR.  It preserves the generated `PUnit` bind as a local let while parsing the yield expression, because the yielded value's de Bruijn indices refer through that binder.

`LeanExe.Examples.Correctness.idRunByteArrayForSum` and `idRunArrayForSum` cover the accepted source form with `let mut` accumulator syntax.  `rejectIdForLoop` remains rejected for `Std.Legacy.Range`, now with a precise unsupported collection-type diagnostic.  `ForInStep.done`, `break`, effects, range loops, polymorphic iterators, and multi-slot accumulators remain outside this slice.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 454 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 454 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Monomorphic recursive instances

The recursive-inductive type representation now records concrete runtime type parameters.  This lets the extractor treat `List UInt64` as a specialized recursive inductive instance rather than as an unsupported polymorphic value.  Constructor extraction splits constructor type parameters from runtime fields, instantiates constructor field domains with the concrete parameter types, and then reuses the existing heap-recursive constructor, matcher, and structural-recursion machinery.

This is not a `List` primitive.  `LeanExe.Examples.Correctness.leanListHeadDemo`, `leanListTailHeadDemo`, and `leanListStructuralSumDemo` use ordinary Lean `List UInt64` literals, pattern matching, helper calls, and direct structural recursion.  Standard `List` library calls such as `map`, `filter`, `foldl`, `any`, `find?`, `concat`, and append still need higher-order specialization or first-order library extraction before they can compile.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 457 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 457 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Direct-lambda List library specialization

Transparent specialization now unfolds nonlocal transparent applications when the application contains a direct lambda argument and the callee is outside the primitive, recursor, and matcher families that the extractor already lowers explicitly.  The purpose is to reduce ordinary library code to the same first-order terms the compiler already accepts, without adding a `List` primitive or a hidden runtime path.  The matcher parser now locates the instantiated scrutinee argument in generated matcher types, which handles polymorphic matchers produced by specialized `List UInt64` library calls.

This slice accepts `LeanExe.Examples.Correctness.leanListMapDemo`, `leanListFilterDemo`, `leanListFindDemo`, and `leanListFindMissingDemo`.  `List.map`, `List.filter`, and `List.find?` compile here because the direct lambdas specialize away and the resulting structural recursion returns first-order data.  At this checkpoint, closed `List.foldl` and direct `List.any` examples still failed because their lowered definitions returned function values from structural recursion.

`List.map` exposed a recursive-value laziness bug in structured branch selection.  `valueIte` previously combined recursive-variant payloads from both branches, which forced inactive recursive constructor payloads and could make a finite list traversal diverge.  Recursive variant branch values now stay behind an `ite` wrapper, so inactive constructor payloads are not evaluated during materialization.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 461 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 461 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Function-valued structural recursion

The structural-recursion extractor now handles generated motives that return function values when those functions can be removed during extraction.  Direct-lambda post arguments are substituted into the generated branch body, and first-order carried post arguments are mapped to explicit helper parameters after the recursive-inductive parameter.  Recursive calls through the generated `PProd.fst` projection now accept the same post arguments, filtering out direct lambdas and passing only first-order carried values to the compiled helper.

The generated matcher parser now chooses the recursive-inductive scrutinee instead of the first supported typed matcher argument, and it treats the final constructor-count arguments after the scrutinee as the branch arms.  This handles both `List.foldl.match_1`, where the accumulator argument precedes the scrutinee, and `List.any.match_1`, where the predicate argument follows the scrutinee.  Constructor detection in generated arm types now searches motive arguments, which covers arm types such as `motive [] p` and preserves the existing nullary-constructor `Unit` binder form.

`LeanExe.Examples.Correctness.leanListFoldlDemo` uses ordinary `List.foldl` over `List UInt64` with a noncommutative decimal accumulator, so the test catches binder-order mistakes.  `leanListAnyDemo` and `leanListAnyMissingDemo` use ordinary `List.any` with direct-lambda predicates.  Direct closed `List.foldl` remains rejected in `rejectLeanListFoldlClosedDemo`, because its initial accumulator would require a hidden carried parameter that the current source-to-WASM function ABI does not synthesize.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 464 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 464 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Compile-time ASCII String expressions

The extractor now treats Lean `String` as a compile-time-only source convenience rather than a supported runtime structure.  `String` is explicitly excluded from the generic structure classifier, so `String` parameters, results, and helper-call ABI slots remain rejected.  Accepted string expressions are ASCII literals, local `String` lets, top-level `String` constants, `String.append`, and append notation through `++`, when the expression is consumed by `String.toUTF8`, `String.length`, `String.isEmpty`, `==`, or `!=`.

This slice deliberately stopped short of an `AsciiString.ofString` helper.  A direct helper with a `String` parameter tempts the generic function path to treat source strings as runtime values, which is the wrong boundary for the current compiler.  Fixed protocol text should use `"field".toUTF8` for `ByteArray` values, and runtime text should enter as `ByteArray` followed by `AsciiString.ofByteArray?` validation.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness LeanExe.Examples.AsciiStringPrograms LeanExe.Examples.JsonCollatzLength LeanExe.Examples.JsonTools`
- [x] `node test/asciistring.js` returned `checked 23 asciistring cases`.
- [x] `node test/core_correctness.js` returned `checked 471 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 46 json program cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 471 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Multi-slot pure for-loop accumulators

Pure `Id.run` `for` loops over `ByteArray` and fixed-width `Array` now carry accumulator values with the normal internal slot layout rather than the previous scalar-only shape.  The extractor reconstructs the accumulator from loop-local slots, extracts the yielded value as a structured value, flattens the body result, and uses multi-slot fold IR whose body stages all result slots before copying them back to the accumulator slots.  The accepted accumulator types include scalars, `Array` pointer values, products, structures, nonrecursive tagged values, and recursive-inductive pointer values, while accumulator shapes containing `ByteArray` remain rejected because pointer and length must be produced atomically.

The binary and WAT emitters gained matching `arrayFoldMultiSlot` and `byteArrayFoldMultiSlot` expression forms for projected slots, plus statement forms that materialize a full structured loop result once into result locals.  Body slots are staged through temporary locals so updates do not observe earlier field writes from the same iteration.  The correctness corpus now covers a `ByteArray` scan carrying a `DigitState` structure, an array scan carrying a `Status` tagged value, and the explicit rejection of a `ByteArray` accumulator.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 474 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Pure range for loops

Pure `Id.run` `for` loops now accept `Std.Legacy.Range` collections in addition to `ByteArray` and fixed-width `Array`.  The extractor reads the checked range structure fields for start, stop, and step, binds the current index as a bounded `Nat`, and reuses the same multi-slot accumulator path used by byte and array loops.  The emitted loop uses exclusive-stop order and checked bounded-`Nat` addition for the index increment.

The IR gained `rangeFoldMultiSlot` expression and statement forms.  The statement form materializes a full structured range-loop result once into result locals, while the expression form covers projected loop results.  The correctness corpus now covers a simple count loop, a stepped range sum, a structured `DigitState` range accumulator, and rejection of a `ByteArray` accumulator in a range loop.

Checks run:

- [x] `lake build`
- [x] `node test/core_correctness.js` returned `checked 477 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 477 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Early-exit pure for loops

Pure `Id.run` `for` loops now retain both parts of the elaborated `ForInStep`: the next accumulator value and the step-completion flag.  The extractor accepts `ForInStep.yield`, `ForInStep.done`, pure wrapping, the generated `PUnit` bind shape used by mutable assignments, and step-level `if` expressions whose branches both produce supported `ForInStep` values.  The correctness corpus covers ordinary `break` in accepted `ByteArray`, fixed-width-array, and range loops without adding a special source-level `break` case to the compiler.

The multi-slot fold IR now carries a `bodyDone` expression.  The binary and WAT emitters evaluate the next accumulator slots into temporary locals, evaluate the done flag before copying those temporaries back to the accumulator slots, copy the accumulator, and branch out of the loop when the flag is true.  Evaluating the done flag before the copy preserves the source view of the old accumulator and current item while still returning the done value as the final accumulator.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 481 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 481 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Continue in pure for loops

Source-level `continue` now compiles in accepted pure `Id.run` `for` loops.  Lean elaborates `continue` to `ForInStep.yield` with the current accumulator, so the existing `ForInStep` parser covers explicit `else` branches.  The no-`else` source form introduces a local joinpoint for the remaining statements in the loop body; the parser now beta-reduces direct lambda joinpoints before parsing the step so code such as `if cond then continue; acc := ...` and `if cond then break; acc := ...` compiles without a compiler-specific source rewrite.

The correctness corpus covers `continue` over `ByteArray`, fixed-width `Array`, and `Std.Legacy.Range`, plus a structured range accumulator.  It also covers a no-`else` `break` before a later assignment, which uses the same joinpoint lowering.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 486 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 486 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Recursive array descent

The extractor now preserves `WellFounded.fix` during local beta specialization, because Lean uses that generated form for recursive descent through an `Array` field.  The new lowering handles the checked shape produced by a recursive function over a tree whose constructor contains `Array self`: the matcher scrutinee is the original function parameter, constructor arms bind the generated well-founded recursive handle, and recursive calls through that handle lower to ordinary WASM self-calls.  `Array.foldl` now recognizes the generated `Array.attach` and `Array.map_unattach.match_1` wrapper, extracting the fold over the underlying array while erasing membership proofs and preserving the callback binder order.

The feature is narrow and recognizes only Lean's generated array-child traversal shape.  The accepted source must be first-order and monomorphic.  Arbitrary `WellFounded.fix`, recursive public ABI values, mutual recursion, and course-of-values traversal through generated below tails remain outside the accepted language.

Checks run:

- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64TreeSizeDemo --out /tmp/u64TreeSizeDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke u64TreeSizeDemo /tmp/u64TreeSizeDemo.wasm` returned `6`.
- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 487 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 487 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Branching structural recursion

Structural-recursion lowering now represents Lean's generated below value as a small projection tree instead of a single recursive handle.  A direct recursive field contributes a pair whose first projection is the recursive result for that field, and branching constructors combine those field pairs with the same right-nested `PProd` shape generated by Lean.  Projection paths such as `x.1.1` and `x.2.1` now lower to separate WASM self-calls on the selected recursive field, while projection into the generated below tail remains rejected as unsupported course-of-values recursion.

`LeanExe.Examples.Correctness.u64BinaryStructuralSizeDemo` covers a binary tree with two direct recursive fields in one constructor.  `LeanExe.Examples.Correctness.u64ExprEvalDemo` covers an expression AST with `lit`, `add`, and `mul`, so the branch-recursion path now supports a representative evaluator shape.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 489 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 489 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke u64BinaryStructuralSizeDemo /tmp/u64BinaryStructuralSizeDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke u64ExprEvalDemo /tmp/u64ExprEvalDemo.wasm` returned `45`.

## 2026-05-12: Closed structural folds

The extractor now lowers a top-level closed structural fold over a list-shaped recursive inductive.  The accepted shape is Lean's generated `brecOn` body with one hidden first-order accumulator, one constructor with a single direct recursive field, and terminal constructors whose arms return the accumulator.  The recursive constructor arm must tail-call the generated below projection for that direct recursive field with the next accumulator value, which gives the compiler a loop over the heap pointer and accumulator slots instead of a synthesized helper function.

This admits direct source such as `leanList123.foldl (fun acc x => acc * 10 + x) 0`.  The lowering is still shape-based rather than a `List` primitive: the code checks the recursive-inductive layout, the generated matcher, the terminal arms, and the recursive-field tail call.  Nested closed structural folds, closed `List.any`, general function-valued motives, and hidden carried arguments outside this one-accumulator fold form remain outside the accepted language.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFoldlClosedDemo --out /tmp/leanListFoldlClosedDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFoldlClosedDemo /tmp/leanListFoldlClosedDemo.wasm` returned `123`.
- [x] `node test/core_correctness.js` returned `checked 490 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 490 accepted, 25 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Closed structural predicates

The extractor now lowers closed structural predicate bodies over list-shaped recursive inductives.  The accepted shape is Lean's generated `brecOn` body with one direct-lambda predicate, one constructor with a single direct recursive field, and terminal constructors that return the predicate identity value.  The recursive constructor arm must combine the predicate result for the current fields with the generated recursive-field result through `Bool.or` for existential predicates or `Bool.and` for universal predicates.

The IR gained `heapLinearPredicate`, which emits a heap-pointer loop with short-circuit behavior.  This remains a structural-recursion lowering rather than a `List` primitive: the extractor checks the recursive-inductive layout, generated matcher, terminal values, predicate lambda, and recursive-field projection before emitting the loop.  The current tests cover direct `List.any` and `List.all` over `List UInt64`, including both short-circuit and terminal cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAnyDirectDemo --out /tmp/leanListAnyDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAnyDirectMissingDemo --out /tmp/leanListAnyDirectMissingDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAllDirectDemo --out /tmp/leanListAllDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAllDirectMissingDemo --out /tmp/leanListAllDirectMissingDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAnyDirectDemo /tmp/leanListAnyDirectDemo.wasm` returned `1`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAnyDirectMissingDemo /tmp/leanListAnyDirectMissingDemo.wasm` returned `0`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAllDirectDemo /tmp/leanListAllDirectDemo.wasm` returned `1`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAllDirectMissingDemo /tmp/leanListAllDirectMissingDemo.wasm` returned `0`.
- [x] `node test/core_correctness.js` returned `checked 495 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 495 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Recursive list-valued helpers

Structural-recursion extraction now preserves the structural-recursion error when a recursive helper fails to lower, instead of trying the closed-fold path for helpers whose first parameter is already the recursive value.  The closed-fold path remains for top-level closed expressions, where it fits the generated `brecOn` shape with a hidden accumulator.  The earlier fallback hid the real failure for a source-defined append helper by reporting a closed-fold tail-call error.

Recursive branch selection now accepts a branch that returns an existing heap recursive value and another branch that constructs a fresh recursive value of the same type.  Flattening already knew how to turn both forms into the internal heap-pointer slot, so the branch combiner now keeps the conditional value lazy and lets result materialization allocate only the selected constructed branch.  This admits source-defined `List UInt64` helpers for length, append, reverse, and fold-right-style traversal.

The regression corpus records direct expression-position standard-library calls as rejected cases: direct `List.map`, `List.filter`, `List.length`, list append notation, `List.reverse`, and `List.foldr`.  Those forms need an expression-position structural-recursion lowering or another principled first-order extraction path.  The accepted cases exercise ordinary source-defined recursive helpers while the compiler remains generic over recursive inductive layouts.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListLengthRecDemo --out /tmp/leanListLengthRecDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAppendRecDemo --out /tmp/leanListAppendRecDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListReverseRecDemo --out /tmp/leanListReverseRecDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFoldrRecDemo --out /tmp/leanListFoldrRecDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListLengthRecDemo /tmp/leanListLengthRecDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendRecDemo /tmp/leanListAppendRecDemo.wasm` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListReverseRecDemo /tmp/leanListReverseRecDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFoldrRecDemo /tmp/leanListFoldrRecDemo.wasm` returned `321`.
- [x] `node test/core_correctness.js` returned `checked 499 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 499 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Expression-position structural recursion

Expression-level `brecOn` terms with no hidden runtime post-arguments now lower through private synthetic helpers.  The collector scans beta-specialized reachable declarations, identifies closed structural-recursion expressions over supported recursive inductive instances, and appends deterministic synthetic functions to the module.  Extraction of the original expression compiles the scrutinee and emits a call to the private helper, while the helper body uses the existing structural-recursion extractor, including generated below projections and WASM self-calls.

This admits direct expression-position `List.map`, `List.filter`, and `List.foldr` over `List UInt64` when the callback specializes to closed first-order code.  The lowering is keyed on recursive-inductive layouts rather than `List` declarations.  `List.length`, list append notation, and `List.reverse` remain rejected because their generated forms do not match this expression-level structural-recursion shape.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListMapDirectDemo --out /tmp/leanListMapDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListMapDirectBranchDemo --out /tmp/leanListMapDirectBranchDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFilterDirectDemo --out /tmp/leanListFilterDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFoldrDemo --out /tmp/leanListFoldrDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListMapDirectDemo /tmp/leanListMapDirectDemo.wasm` returned `2`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListMapDirectBranchDemo /tmp/leanListMapDirectBranchDemo.wasm 0` returned `10`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListMapDirectBranchDemo /tmp/leanListMapDirectBranchDemo.wasm 1` returned `2`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFilterDirectDemo /tmp/leanListFilterDirectDemo.wasm` returned `2`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFoldrDemo /tmp/leanListFoldrDemo.wasm` returned `321`.
- [x] `node test/core_correctness.js` returned `checked 504 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 504 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Structural recursion with post-arguments

Expression-level structural-recursion lowering now synthesizes helpers that accept supported first-order post-arguments after the recursive scrutinee.  The discovery pass reduces transparent wrapper definitions only far enough to expose a supported recursive-inductive `brecOn`; it reduces projection and constructor adapters for typeclass methods, preserves default runtime arguments, and leaves the existing primitive extractors responsible for ordinary arithmetic, string, array, and byte-array operations.  The synthetic helper body replaces dynamic post-arguments with helper parameters, while direct-lambda post-arguments remain static when they are closed.

This admits direct `List.length`, list append notation through `++`, and `List.reverse` over `List UInt64` without adding compiler cases for those declarations.  The append branch example passes the right-hand list as a runtime carried value, which exercises the new post-argument path rather than a closed literal.  Runtime `Char` is now rejected by the type classifier, so compile-time string helpers such as `String.length` continue to use the string-specific ASCII path instead of being captured as generic `List Char` recursion.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListLengthDirectDemo --out /tmp/leanListLengthDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAppendDirectDemo --out /tmp/leanListAppendDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAppendDirectBranchDemo --out /tmp/leanListAppendDirectBranchDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListReverseDirectDemo --out /tmp/leanListReverseDirectDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListLengthDirectDemo /tmp/leanListLengthDirectDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendDirectDemo /tmp/leanListAppendDirectDemo.wasm` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendDirectBranchDemo /tmp/leanListAppendDirectBranchDemo.wasm 0` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendDirectBranchDemo /tmp/leanListAppendDirectBranchDemo.wasm 1` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListReverseDirectDemo /tmp/leanListReverseDirectDemo.wasm` returned `3`.
- [x] `node test/core_correctness.js` returned `checked 509 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 509 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Shared structural-recursion parsing

The extractor now parses recursive-inductive `brecOn` applications through `rawStructuralRecApplication?`, with `structuralRecApplication?` adding normalization for expression-position terms.  The shared record holds the constant, type arguments, motive, scrutinee, step, and post-arguments that the expression-level synthetic helper path, closed predicate path, closed fold path, top-level structural-recursion extractor, and top-level candidate detector decoded separately.  The regression counts stayed unchanged, which matches the intent of this refactor: one parser now supplies the existing lowering paths.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 509 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 509 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Recursive pointers in fixed-width values

Internal fixed-width structures and nonrecursive tagged values can contain recursive-inductive fields because the existing layout machinery treats a recursive value as one heap-pointer slot at strict boundaries.  This is now covered by `ExprBox`, which stores a `U64Expr` inside a structure and exercises direct use plus `Array ExprBox` folding, and by `ExprSlot`, which stores a `U64Expr` inside a tagged payload and exercises direct matching plus `Array.find?`.  The public ABI still rejects those layouts when they appear as entry parameters or results, so the feature remains internal until recursive data has a documented host representation.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveStructFieldDemo --out /tmp/recursiveStructFieldDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveStructArrayFoldDemo --out /tmp/recursiveStructArrayFoldDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveTaggedPayloadDemo --out /tmp/recursiveTaggedPayloadDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveTaggedArrayFindDemo --out /tmp/recursiveTaggedArrayFindDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveStructFieldDemo /tmp/recursiveStructFieldDemo.wasm` returned `21`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveStructArrayFoldDemo /tmp/recursiveStructArrayFoldDemo.wasm` returned `24`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveTaggedPayloadDemo /tmp/recursiveTaggedPayloadDemo.wasm` returned `17`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveTaggedArrayFindDemo /tmp/recursiveTaggedArrayFindDemo.wasm` returned `19`.
- [x] `node test/core_correctness.js` returned `checked 513 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 513 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Internal mutual recursive inductives

Recursive-inductive layout classification now uses Lean's `InductiveVal.all` family list.  A field inside a recursive family may refer to any member of the same specialized family, so a `MutJson` constructor can store an `Array MutField`, and a `MutField` constructor can store a `MutJson`.  Each family member still lowers to the existing one-slot heap-pointer representation at strict boundaries.  At this point, public entry parameters and results still rejected recursive-family values, and mutual structural recursion and mutual recursive helper functions remained outside the accepted language.

The correctness corpus now includes a `MutJson` and `MutField` pair, direct array construction over `MutJson`, object-like arrays over `MutField`, a structure wrapper around `MutField`, a tagged wrapper around `MutJson`, and public ABI rejection cases for both family members and arrays of family members.  Sparse constructor matches still lower to generated helpers outside the current matcher path, so the accepted examples use exhaustive matches.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualJsonArrayDemo --out /tmp/mutualJsonArrayDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualJsonObjectDemo --out /tmp/mutualJsonObjectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualWrappedFieldArrayDemo --out /tmp/mutualWrappedFieldArrayDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualTaggedArrayFindDemo --out /tmp/mutualTaggedArrayFindDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualJsonArrayDemo /tmp/mutualJsonArrayDemo.wasm` returned `4`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualJsonObjectDemo /tmp/mutualJsonObjectDemo.wasm` returned `60`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualWrappedFieldArrayDemo /tmp/mutualWrappedFieldArrayDemo.wasm` returned `55`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualTaggedArrayFindDemo /tmp/mutualTaggedArrayFindDemo.wasm` returned `102`.
- [x] `node test/core_correctness.js` returned `checked 517 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 517 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Two-branch mutual structural recursion

Ordinary two-function mutual structural recursion over two members of the same recursive family now compiles through Lean's generated `WellFounded.Nat.fix` helper over `PSum`.  The extractor treats `PSum` as an internal sum layout, compiles the generated mutual helper as an internal function with tag-plus-payload parameters, and consumes the hidden well-founded binder in each member's generated constructor matcher.  Recursive calls inside those constructor arms use the same well-founded handle, including calls inside fixed-width `Array.attach` folds over family members.

The correctness corpus now includes `mutJsonDeepSize` and `mutFieldDeepSize`, which traverse `MutJson` and `MutField` through both direct fields and arrays.  The supported shape is still narrow: it covers the binary `PSum` helper that Lean generates for ordinary two-function mutual definitions.  Broader mutual groups, non-family `PSum` recursion, public recursive values, and arbitrary well-founded recursion remain outside the accepted language.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralJsonSizeDemo --out /tmp/mutualStructuralJsonSizeDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralFieldSizeDemo --out /tmp/mutualStructuralFieldSizeDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualStructuralJsonSizeDemo /tmp/mutualStructuralJsonSizeDemo.wasm` returned `10`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualStructuralFieldSizeDemo /tmp/mutualStructuralFieldSizeDemo.wasm` returned `11`.
- [x] `node test/core_correctness.js` returned `checked 519 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 519 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: N-way mutual structural recursion

Lean lowers ordinary mutual definitions over three or more recursive-family members with a right-nested `PSum` parameter, such as `PSum A (PSum B C)`, and a single generated `WellFounded.Nat.fix` helper.  The extractor now parses that nested `PSum.casesOn` tree recursively.  Each leaf must still match one supported recursive-family member, and each member branch still goes through the existing generated-matcher checks for direct recursive fields and fixed-width `Array.attach` folds.

The correctness corpus now includes `TriA`, `TriB`, and `TriC`, a three-member recursive family whose constructors recurse through arrays.  `triAScore`, `triBScore`, and `triCScore` compile through the shared generated helper and produce independent entry demos for all three wrapper functions.  The accepted shape remains the Lean-generated structural form; arbitrary well-founded recursion, non-family `PSum` recursion, public recursive values, and mutual helper groups that do not structurally descend through recursive-family values remain outside the accepted language.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralTriADemo --out .lake/build/mutual-tri-a.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralTriBDemo --out .lake/build/mutual-tri-b.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralTriCDemo --out .lake/build/mutual-tri-c.wasm`
- [x] `build/tools/wasmtime/current/wasmtime run --invoke mutualStructuralTriADemo .lake/build/mutual-tri-a.wasm` returned `21`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke mutualStructuralTriBDemo .lake/build/mutual-tri-b.wasm` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke mutualStructuralTriCDemo .lake/build/mutual-tri-c.wasm` returned `15`.
- [x] `node test/core_correctness.js` returned `checked 522 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 522 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Concrete parameters for data layouts

User-defined structures and nonrecursive inductives now carry concrete runtime type arguments in the extracted `Ty` representation.  The extractor reconstructs the instantiated Lean type when substituting constructor fields, projection targets, matcher scrutinees, helper parameters, helper results, and array element layouts.  This fixes nested cases such as `ParamResult UInt64 (Box UInt64)`, where rebuilding the type as bare `Box` lost the `UInt64` argument and made constructor payload classification fail.

Lean registered structures now use `isStructure`, while ordinary one-constructor inductives stay on the user-inductive path.  This distinction matters because Lean's `isStructureLike` also returns true for nonrecursive single-constructor inductives with no indices, but only registered structures have field metadata for `getStructureFieldsFlattened`.  The bug surfaced through `CheckedPayload`, a one-constructor inductive with a proof-erased field, which must compile as a tagged value rather than as a structure.

Concrete parametric structures also exposed a dependency-collection boundary around type-class evidence.  `Inhabited Slot` became a supported structure-shaped type once parametric structures were allowed, which pulled the derived `instInhabitedSlot.default` helper into the compiled call graph for array bang indexing.  Evidence carrier types such as `Inhabited`, `BEq`, arithmetic classes, ordering classes, and `GetElem` classes are now rejected as runtime data, so primitive extractors consume their applications without compiling the instance values as ordinary helpers.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 537 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 537 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Inline specialization for polymorphic helpers

The extractor now recognizes local first-order polymorphic helper applications whose static type or proof arguments precede all runtime arguments.  At a concrete call site, it substitutes those static arguments into the helper body, derives the concrete runtime parameter and result types from the instantiated function type, and reuses the existing inline extraction path for the remaining runtime arguments.  This keeps the first slice small: there is no shared generic runtime function, no typeclass specialization, and no escaping function value.

The specialized inline path preserves the existing lazy argument behavior.  The correctness corpus includes a polymorphic helper that returns the first `Box` value while the unused second `Box` contains an out-of-bounds array read; the generated WASM returns the first value rather than evaluating the unused argument.  Other examples cover `Box α -> α`, projections from `PairBox α β`, boolean matching over `ParamResult ε α`, extracting a `Point` through a polymorphic result helper, and extracting a value from `CheckedPayload α`.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 543 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 543 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Layout-driven internal array elements

The extractor now has an explicit `ValueLayout` model for scalar, fixed-width, and pointer-shaped runtime values.  Array element widths come from that layout instead of from a hand-written list of surface types.  Internal arrays can store nested arrays as one pointer slot, products as their flattened slot sequence, and structures or tagged values whose fields include array or recursive pointer slots.

The public array ABI remains conservative.  Entry parameters and results still accept scalar, structure, and tagged fixed-width array elements only when their layouts contain no nested heap references.  The correctness corpus now includes public rejection cases for nested-array parameters, nested-array results, and arrays of structures that contain array fields.

This work exposed an older internal-call layout bug.  Non-exported helper functions now use internal parameter and result layouts, so products and other internal-only multi-slot values can cross real WASM calls without being treated as public ABI values.  The inline decision also checks strict materialization safety for multi-slot arguments, preserving lazy projection behavior when an unused field contains a trapping expression.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 550 accepted, 32 rejected, and 13 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.nestedArrayMapPushRead --out /tmp/nestedArrayMapPushRead.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayBoxElementRead --out /tmp/arrayBoxElementRead.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProductElementRead --out /tmp/arrayProductElementRead.wasm`
- [x] `build/tools/wasmtime/current/wasmtime run --invoke nestedArrayMapPushRead /tmp/nestedArrayMapPushRead.wasm` returned `299`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke arrayBoxElementRead /tmp/arrayBoxElementRead.wasm` returned `223`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke arrayProductElementRead /tmp/arrayProductElementRead.wasm` returned `43`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 550 accepted, 32 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Structured direct fold accumulators

Direct `Array.foldl` and `ByteArray.foldl` now use the same internal-slot accumulator model as accepted pure `Id.run` `for` loops.  The extractor reconstructs the accumulator from loop-local slots, extracts the direct-lambda body as a structured value, flattens the body result, and rebuilds the requested source-level result value from the projected fold slots.  At this checkpoint, supported accumulator shapes were scalars, supported array pointers, products, structures, nonrecursive tagged values, and recursive-inductive pointer values, provided the flattened accumulator contained no `ByteArray` field.

The correctness corpus now covers direct folds carrying a `CountSum` structure, a product, a `Status` tagged value, and an array pointer.  It covers both `Array.foldl` and `ByteArray.foldl`, and it rejected direct folds whose accumulator was a `ByteArray`.  The later `ByteArray` accumulator entry supersedes that limitation.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 558 accepted, 34 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Unified direct fold lowering

The scalar-only direct fold path has been removed.  `extractExprFrom` now handles scalar uses of `Array.foldl` and `ByteArray.foldl` by extracting the same value-level fold representation used for structured accumulators, then projecting the scalar result.  The IR and WASM emitters no longer contain the old one-slot `arrayFoldSlots` and `byteArrayFold` expression forms.

The shared accumulator predicate is now named `supportedLoopAccumulatorType`, because pure `for` loops and direct folds use the same accumulator layout.  Existing scalar fold correctness cases now exercise the multi-slot fold IR with result width one, while the structured fold cases exercise the same code path at larger widths.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 558 accepted, 34 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldSum --out .lake/build/core-correctness/arrayFoldSum.unified.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayFoldSum --out .lake/build/core-correctness/byteArrayFoldSum.unified.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldSum --out .lake/build/core-correctness/arrayFoldSum.unified.wat`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldSum .lake/build/core-correctness/arrayFoldSum.unified.wasm` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke byteArrayFoldSum .lake/build/core-correctness/byteArrayFoldSum.unified.wasm` returned `6`.
- [x] `wc -c .lake/build/core-correctness/arrayFoldSum.unified.wat` returned `11373`.

## 2026-05-13: Slot-width array IR cleanup

The one-slot array expression forms have been removed from the IR and the WASM emitters.  Scalar arrays now use the same slot-width representation as arrays of products, structures, tagged values, recursive pointers, and nested array pointers, with scalar elements represented as width one.  Scalar reads from primitive `Array` indexing lower to `arrayGetSlot 1 0`, so extraction no longer needs a separate scalar array read constructor.

This removes the duplicate allocation, replication, update, push, pop, append, extract, map, insert, erase, swap, and reverse emitter paths.  The remaining array representation still stores the logical length in the array header and stores the element payload as `length * width` contiguous 64-bit cells.  The public ABI restrictions remain unchanged: nested heap references may appear in internal arrays but still cannot cross exported function boundaries as public array parameters or results.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 558 accepted, 34 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-14: ByteArray loop and fold accumulators

`ByteArray` now participates in the shared internal accumulator layout for pure `Id.run` `for` loops, `Array.foldl`, and `ByteArray.foldl`.  The representation uses the existing two-slot pointer-length value, so byte-producing loops and folds require no new WASM expression form.  Products, structures, and tagged values can carry `ByteArray` fields through the same accumulator path when their other fields are supported.

The correctness corpus now covers byte-producing `ByteArray` loops, `break`, `continue`, range loops, `Array.foldl` with a `ByteArray` accumulator, `ByteArray.foldl` with a `ByteArray` accumulator, and structures that carry a `ByteArray` field as part of the accumulator.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 566 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 566 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldStructAccumulator --out .lake/build/core-correctness/arrayFoldStructAccumulator.wasmtime.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayFoldStatusAccumulator --out .lake/build/core-correctness/byteArrayFoldStatusAccumulator.wasmtime.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldStructAccumulator .lake/build/core-correctness/arrayFoldStructAccumulator.wasmtime.wasm` returned `36`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke byteArrayFoldStatusAccumulator .lake/build/core-correctness/byteArrayFoldStatusAccumulator.wasmtime.wasm` returned `24`.

## 2026-05-14: Public UInt8 and UInt32 ABI

`UInt8` and `UInt32` now cross the public entry ABI as one `i64` slot each.  Public parameters normalize at function entry by masking to `2^8 - 1` or `2^32 - 1`, and public results normalize before returning to the host.  This matches the fixed-width representation already used by literals, conversions, arithmetic, arrays, and byte-oriented helper code inside the compiler subset.

The former public-scalar rejection fixtures now compile as ordinary examples.  `uint8ParamToNat` and `uint32ParamToNat` test parameter normalization from oversized host arguments, while `uint8Return` and `uint32Return` test result normalization from oversized Lean literals.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 570 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint8ParamToNat .lake/build/core-correctness/uint8ParamToNat.public.wasm 300` returned `44`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint8Return .lake/build/core-correctness/uint8Return.public.wasm` returned `44`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint32ParamToNat .lake/build/core-correctness/uint32ParamToNat.public.wasm 4294967297` returned `1`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint32Return .lake/build/core-correctness/uint32Return.public.wasm` returned `1`.

## 2026-05-14: WASI ByteArray stdout programs

`compile-wasi` adds a command-style target for pure entries that take no parameters and return `ByteArray`.  The generated module imports `wasi_snapshot_preview1.fd_write`, exports `_start`, calls the compiled Lean entry, writes the returned byte range to stdout, and traps when `fd_write` reports an error or a short write.  This keeps Lean `IO` outside the source language while giving byte-producing programs observable output under Wasmtime.

The WASI target reuses the same extracted function bodies as library mode.  Because imported functions occupy the start of the WASM function-index space, the emitter shifts internal call indices by the number of imports before encoding command modules.  The command module exports memory and `_start`; it does not expose the selected Lean entry, `alloc`, or `reset` as its program interface.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 570 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 4 WASI program cases and 2 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 4 WASI program cases and 2 rejections`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile-wasi --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn --out .lake/build/core-correctness/byteArrayStringConstReturn.wasi.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayAppendReturn --out .lake/build/core-correctness/byteArrayAppendReturn.wasi.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayPushSize --out .lake/build/core-correctness/bad-non-bytearray.wasm` rejected with `program entry must return ByteArray`.
- [x] `build/tools/wasmtime/current/wasmtime run .lake/build/core-correctness/byteArrayStringConstReturn.wasi.wasm` returned `XYZ`.
- [x] `build/tools/wasmtime/current/wasmtime run .lake/build/core-correctness/byteArrayAppendReturn.wasi.wasm` returned `ABC`.

## 2026-05-14: WASI bounded stdin programs

`compile-wasi-stdin` adds a bounded stdin-to-stdout command target for pure entries of type `ByteArray -> ByteArray`.  The generated `_start` imports `wasi_snapshot_preview1.fd_read` and `fd_write`, reads stdin into the arena until EOF, traps if input exceeds the explicit `--max-input-bytes` limit, calls the compiled Lean entry with the input pointer and length, and writes the returned byte range to stdout.  This keeps input effects in the generated adapter rather than in Lean source code.

The adapter reserves `max-input-bytes + 1` bytes so it can distinguish EOF exactly at the limit from input that exceeds the limit.  The maximum configured limit must fit in the initial 16-page memory after the arena start at byte offset `4096`.  Imported functions shift the WASM function-index space by two for stdin modules, so the emitter reuses the existing call-index shifter with offset `2`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayIdentityReturn --out .lake/build/wasi-programs/byteArrayIdentityReturn.stdin.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.appendBang --out .lake/build/wasi-programs/appendBang.stdin.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.tailSlice --out .lake/build/wasi-programs/tailSlice.stdin.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn --out .lake/build/wasi-programs/bad-stdin-shape.wasm` rejected with `program stdin entry must have type ByteArray -> ByteArray`.
- [x] `compile-wasi-stdin` rejects `--max-input-bytes 1048576` with `max input bytes exceeds WASM memory capacity`.
- [x] `printf AB | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/byteArrayIdentityReturn.stdin.wasm` returned `AB`.
- [x] `printf AB | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/appendBang.stdin.wasm` returned `AB!`.
- [x] `printf ABC | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/tailSlice.stdin.wasm` returned `BC`.
- [x] `printf ABCDEFGHI | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/byteArrayIdentityReturn.stdin.wasm` trapped on input limit.
- [x] `node test/wasi_program.js` returned `checked 7 WASI program cases, 1 stdin trap, and 4 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 7 WASI program cases, 1 stdin trap, and 4 rejections`, and `checked 56 cases`.

## 2026-05-14: WASI error-result programs

`compile-wasi-stdin-except` adds a command target for pure entries of type `ByteArray -> Except ByteArray ByteArray`.  The generated `_start` uses the same bounded `fd_read` input path as `compile-wasi-stdin`.  It decodes the public `Except` result as tag, error pointer, error length, ok pointer, and ok length.  Tag `1` writes the ok payload to stdout and returns normally.  Tag `0` writes the error payload to stderr and calls `wasi_snapshot_preview1.proc_exit` with status `1`.

The WASI emitter now builds command-module type sections from an explicit list of import function types.  `fd_read` and `fd_write` share the `[i32, i32, i32, i32] -> i32` type, while `proc_exit` uses `[i32] -> []`.  Module function type indices start after those import types, and module function indices start after the imported functions, so the existing call-index shifter still has one concrete offset per command adapter.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/wasi_program.js` returned `checked 9 WASI program cases, 1 stdin trap, and 5 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 9 WASI program cases, 1 stdin trap, and 5 rejections`, and `checked 56 cases`.

## 2026-05-14: WASI argv programs

`Array ByteArray` is now a supported internal array shape.  Each element stores two slots, the byte pointer and byte length, using the same internal `ByteArray` representation used for locals and helper calls.  Public `Array ByteArray` parameters and results remain rejected because the library-mode host ABI still excludes arrays with heap-reference elements.

`compile-wasi-argv-except` adds a command target for pure entries of type `Array ByteArray -> Except ByteArray ByteArray`.  The generated `_start` imports `args_sizes_get`, `args_get`, `fd_write`, and `proc_exit`.  It allocates a fixed arena region from the configured `--max-args` and `--max-argv-bytes`, reads WASI argv into that region, skips `argv[0]`, builds an internal array of user-argument byte slices, calls the Lean entry, writes `Except.ok` bytes to stdout, and writes `Except.error` bytes to stderr before `proc_exit 1`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 574 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 11 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 11 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: JSON tree pipeline

`LeanExe.Examples.JsonTreeCommand` adds a two-command JSON pipeline.  `makeTree` reads a JSON array through `compile-wasi-stdin-except`, builds a source-level recursive binary-search tree, and writes the tree as nested JSON.  `searchTree` reads that tree JSON through stdin, reads the search key from argv through `compile-wasi-stdin-argv-except`, and writes a JSON boolean result.

The example exposed three compiler issues.  Structural recursion with captured non-scrutinee parameters now passes those parameters through direct recursive-field calls, which lets ordinary definitions such as `insert tree value` compile without source reshaping.  Fuel recursion now lowers tail-position control flow under nested `if`, dependent `if`, `Bool` matches, `Option` matches, and supported nonrecursive inductive matches, which lets parser-style loops return early or recur from natural source branches.

The same example also exposed duplicated evaluation of byte-array operand expressions.  `ByteArray.push`, `ByteArray.append`, and byte-array append notation now bind operand pointer-length pairs before constructing the result, so a recursive byte-producing helper used as an operand runs once.  The stdin-plus-argv WASI adapter now aligns the arena before building the argv pointer table, matching the alignment expected by WASI `args_get`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.makeTree --out .lake/build/make-tree.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except --max-input-bytes 8192 --max-args 8 --max-argv-bytes 256 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.searchTree --out .lake/build/search-tree.wasm`
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/make-tree.wasm | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/search-tree.wasm 4` returned `{"found":true}`.
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/make-tree.wasm | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/search-tree.wasm 7` returned `{"found":false}`.

## 2026-05-14: Reference-counted heap runtime

Library-mode modules now allocate heap-backed payloads behind a small reference-counted header in WASM linear memory.  The payload pointer remains the public pointer, so array length headers and byte-array contents keep their existing ABI positions.  The runtime stores reference count, payload capacity, object kind, and two descriptor fields immediately before the payload, and it reuses released blocks through a first-fit free list.

The library ABI now exports `retain`, `release`, and `free` in addition to `alloc` and `reset`.  `alloc` creates a raw byte object with count `1`, `retain` increments a nonzero object's count and returns the same pointer, and `release` decrements the count and returns the block to the free list at zero.  `free` is an alias for `release` for hosts that expect that name.

This is the runtime foundation for compiler-emitted reclamation, not full ownership analysis.  Generated code now gives byte arrays, arrays, and recursive-inductive heap objects RC headers, and hosts can release returned objects.  The compiler still needs a type-directed ownership pass before it can release dead internal temporaries inside one call without risking use-after-free.

Checks run:

- [x] `lake build`
- [x] `node test/refcount.js` returned `checked 3 refcount cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 3 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 19 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: Conservative compiler-emitted releases

The IR now has a `release` statement, and the binary emitter passes the runtime release-function index into user-function emission.  Library modules call the exported release runtime.  WASI command modules define the same release runtime after `_start`, so compiled user functions have a valid target when the extractor emits a release in command mode.

The extractor emits releases for a narrow ownership case: a local expression or local binding must assign a value whose final expression returns a fresh heap allocation, and the surrounding function result type must contain no heap pointer.  This keeps returned heap values conservative while reclaiming scalar-result temporaries such as `let a := Array.replicate 1 (5 : UInt64); ... a[0]! ...`.  The pass follows expression lets to find the allocated value and handles one-slot heap allocations inside `LocalLet.slots`.  It does not release call results, loop-carried values, heap-pointer result aliases, or values whose last use occurs before the final result assignment.

`test/refcount.js` now checks this compiler path by compiling `LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray`, calling it with a byte-array input, and verifying that the next 16-byte allocation reuses the internal array block.  The test derives the expected block location from allocator behavior after `reset()`, rather than from a hard-coded header size.

Checks run:

- [x] `lake build`
- [x] `node test/refcount.js` returned `checked 4 refcount cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 4 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 19 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-15: Array child release for recursive values

Array allocation now records a child mask for recursive-inductive pointer slots in the fixed-width element layout.  The mask follows products, structures, and nonrecursive tagged values, but it does not mark `ByteArray` fields or nested array fields.  Those pointer shapes can name borrowed input storage, byte-array slices, or WASI adapter arrays, so treating them as owned RC roots would make correct programs trap.

Array-producing operations now retain recursive child pointers when they copy existing elements into a new array.  Inserted values also carry an owned-child mask, so a freshly constructed recursive value can be transferred into the new array without an extra retain while a borrowed recursive value is retained before sharing.  `Array.replicate` treats the first replicated owned child as the transferred reference and retains the remaining references.

`LeanExe.Runtime.release` now accepts compiler-owned array roots as well as monomorphic recursive-inductive roots.  The ownership precondition is unchanged: source code must release only a value that will not be used again, and the compiler does not prove that condition.  Releasing a host-owned public array pointer or a WASI adapter array violates the runtime representation and may trap.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64ListArrayRuntimeReleaseFrees --out .lake/build/u64ListArrayRuntimeReleaseFrees.wasm`
- [x] `build/tools/wasmtime/current/wasmtime run --invoke u64ListArrayRuntimeReleaseFrees .lake/build/u64ListArrayRuntimeReleaseFrees.wasm` returned `103`.
- [x] `node test/core_correctness.js` returned `checked 611 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 611 accepted, 29 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: ByteArray owner slots in stored values

`ByteArray` now has separate public and internal layouts.  Public entry parameters and results still use pointer and length slots, which keeps the host ABI stable.  Internal values use owner, pointer, and length slots, where owner `0` marks borrowed storage and a nonzero owner names the reference-counted allocation root.

Byte-array constructors that allocate new buffers set owner equal to the allocated pointer.  `ByteArray.extract` preserves the source owner while changing the visible pointer and length, so a slice stored in an array, structure, or tagged value can keep the root allocation alive.  The release child mask now marks `ByteArray` owner slots in recursive values and fixed-width array elements, while nested array fields remain outside recursive release until their representation carries equivalent owner metadata.

The extractor also tracks owned aliases through local `let` bindings when it decides whether a child slot transfers ownership into a newly allocated array or heap object.  Explicit `LeanExe.Runtime.release` calls suppress compiler-emitted cleanup for the released slot, which prevents a user-declared ownership boundary from being followed by an automatic second release.  The WASI argv adapters now build internal `Array ByteArray` values with three-slot elements and consume the seven-slot internal result for `Except ByteArray ByteArray` entries.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 612 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/refcount.js` returned `checked 6 refcount cases`.
- [x] `lake build LeanExe.Wasm.Binary LeanExe.Examples.ByteArrayPrograms lean-wasm`
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 612 accepted, 29 rejected, and 13 trapped cases`, `checked 6 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Owned helper-call result cleanup

The release pass now reclaims owner slots from helper-call results in scalar-result functions when the callee has no heap-bearing parameters.  This covers helper results such as an owned `Array UInt64`, an owned `ByteArray`, or a fixed-width structure containing both, while avoiding helpers such as `AsciiString.ofTrustedByteArray` that return a borrowed owner from a caller-owned byte array.  The rule is conservative because the compiler still lacks a helper-result ownership summary.

This work also fixed internal result materialization for heap fields inside structures and tagged values.  A structure result that contains `Array` or `ByteArray` fields now evaluates each inline heap field once, then copies owner and pointer slots from that one local value.  Without that rule, one field expression could allocate separately for the owner slot and visible pointer slot, which made later release either leak or reclaim the wrong allocation.

The GC tree rewrite WASI test now allows nonzero frees before the explicit rewrite loop.  Compiler-emitted cleanup can release temporary helper-call results before that metric is sampled, so the test checks the invariant that allocations exceed initial frees and that later explicit releases advance the counters.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/refcount.js` returned `checked 14 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 617 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/asciistring.js` returned `checked 23 asciistring cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Extractor module split

`LeanExe.Extract.Core` now imports two new modules that keep public declarations in the same namespace.  `Types.lean` contains the core aliases, signatures, extracted values, binding context, type recognition, layout rules, supported type predicates, and reachability helpers.  `Values.lean` contains binding lookup, primitive recognition, liveness pruning, value flattening, ownership and release analysis, and result materialization.

This first split preserves declaration names and behavior.  It reduces `Core.lean` from 12,696 to 9,168 lines and creates a boundary before heap loading and expression extraction.  Later splits can move heap loading, array and byte-array lowering, matcher decoding, demand analysis, and recursion lowering without mixing redesign into the mechanical refactor.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Captured structural recursion

Expression-position structural recursion now records loose de Bruijn variables in the generated motive, step, and direct-lambda post-arguments.  When those loose variables refer to supported first-order locals, the extractor synthesizes a private helper whose first parameter is the recursive scrutinee and whose later parameters carry the captured values.  The synthetic helper rebases the captured references into that new parameter context, so recursive calls produced from Lean's generated below value reuse the same captured values.

The correctness examples now exercise recursive-data programs that return structures, map and transform binary trees, return `Option U64Binary` and `Except UInt64 U64Binary`, and use a tree predicate with a non-recursive `needle` parameter before the recursive tree argument.  The last case exposed the original failure mode: the extractor had generated a synthetic helper whose step still referenced the outer `needle` binder, producing an unbound de Bruijn variable during extraction.  The fix keeps the source program shape ordinary Lean code rather than rewriting examples to put the recursive argument first.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 627 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 47 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 627 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Storage lowering module split

`LeanExe.Extract.Storage` now contains heap loads, field flattening from runtime field kinds, array-element flattening, strict-slot materialization, array load/find/local reconstruction, internal-slot reconstruction, public and internal parameter bindings, function parameter targets, and constructor-field binding helpers.  `Core.lean` imports that module and now begins with generic matcher and control-flow helpers.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 9,168 to 8,496 lines.  The next clean boundary is matcher decoding because `Core.lean` now opens with helpers for `Option`, `Except`, `ForIn`, generated matchers, structures, and variants.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Pattern recognition module split

`LeanExe.Extract.Patterns` now contains constructor type helpers, monad and `ForIn` recognition, array-attach generated matcher helpers, list literal recognition, generated matcher scrutinee discovery, and matcher decoding for `Option`, `Except`, `Bool`, `Nat`, products, `PSum`, structures, and variants.  `Core.lean` imports that module and now begins with demand analysis.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 8,496 to 7,694 lines.  Demand analysis is now the next clean module boundary, followed by structural and well-founded recursion lowering.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Demand analysis module split

`LeanExe.Extract.Demand` now contains the demand-set helpers, `Demand`, `DemandSummary`, structural equality demand helpers, expression and condition demand analysis, `demandSummary`, `mayTrapExpr`, and strict-call materialization checks.  `Core.lean` imports that module and now begins with structural-recursion recognition and lowering.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 7,694 to 6,627 lines.  Structural recursion is now the next clean module boundary; after that, well-founded and Nat recursion lowering can move into a second recursion-focused module or a sibling module.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Structural recursion module split

`LeanExe.Extract.StructuralRec` now contains `brecOn` recognition, structural normalization, expression-shaped structural recursion synthesis, structural matcher parsing, recursive-field below bindings, structural arm binder consumption, closed structural predicate shape recognition, and Nat recursor projection recognition.  `Core.lean` imports that module and now begins with the extraction mutual block.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 6,627 to 6,015 lines.  The next boundary is the extraction mutual block itself; it should be split with more care because it contains value extraction, scalar extraction, condition extraction, and primitive lowering in one mutual recursion.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.
