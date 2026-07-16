# Development Journal

## 2026-06-19: Talos Proof for Generated GCD WASM

`LeanExe.Examples.TalosGcd.gcd` is a small Euclidean GCD program written in the supported Lean subset.  The LeanExe compiler emits the WASM artifact stored at `proofs/talos-gcd/rust/build/gcd/program.wasm`; `wasm-tools print` produces the WAT that Talos decodes into `Project.Gcd.Program`.  The proof in `proofs/talos-gcd/lean/Project/Gcd/Spec.lean` states that exported function `0` terminates for all `UInt64` inputs and returns `UInt64.ofNat (Nat.gcd a.toNat b.toNat)`.

The proof follows the generated WASM, including the compiler’s Boolean-normalization blocks, rather than a hand-written WAT model.  Its loop invariant names the generated local frame, treats WASM locals `4` and `5` as the Euclidean state, leaves scratch locals unconstrained, and uses `y.toNat` as the decreasing measure.  The generated module includes LeanExe runtime exports, but the `gcd` export itself does not touch memory or call runtime functions, so the spec is store-parametric.

`tools/check-talos-gcd.sh` is the integrity check for this proof slice.  It rebuilds the Lean source with `lean-wasm`, emits a fresh WASM file, prints fresh WAT with `wasm-tools`, compares both files against the Talos proof inputs, and then rebuilds the Talos Lean proof project.  The script accepts `WASM_TOOLS` or finds `$HOME/.cargo/bin/wasm-tools`, because `cargo install` does not guarantee the binary is on the noninteractive shell path.

Checks run:

- [x] `bash tools/check-talos-gcd.sh` rebuilt `LeanExe.Examples.TalosGcd`, compared regenerated WASM and WAT against `proofs/talos-gcd/rust/build/gcd/`, and built the Talos proof project.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos-gcd/rust/build/gcd/program.wasm 48 18` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos-gcd/rust/build/gcd/program.wasm 270 192` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos-gcd/rust/build/gcd/program.wasm 17 0` returned `17`.

## 2026-06-16: Helper Result Owner Aliases

The orderbook WASM harness exposed a release-analysis bug in functions that return heap-bearing structures assembled from helper results.  The reduced case was a depth state with `bids` and `asks` arrays: the recursive helper returned one accumulator array unchanged, while the caller copied the helper result into a `DepthResult` and then released the original empty array local.  Rendering the returned result then read a freed empty array; empty stdin produced corrupt depth output, and non-empty stdin trapped in Wasmtime.

Release analysis now expands returned owner slots through local lets and helper calls before deciding which non-recursive owned temporaries can be released.  A helper call contributes its argument slots to that expansion only when the helper has heap parameters and at least one heap result owner that the existing fresh-result summary does not prove fresh.  This keeps the existing release behavior for helpers that return newly allocated arrays or byte arrays, while preserving argument-owned roots returned through accumulator helpers.

The new `depthAliasRun` WASI example in `LeanExe.Examples.Correctness` keeps the failing shape without importing the orderbook module.  It selects a bid-only or ask-only book from stdin, computes old-style depth through a two-array state, and renders both sides into `ByteArray`.  Before the fix, empty stdin emitted the corrupt sequence beginning `0 1 12 6 48 5501223100278326855`, and stdin `x` trapped at `wasm unreachable`; after the fix, the outputs are `0 1 12 6 0\n` and `0 0 1 100 6\n`.

Checks run:

- [x] `lake build LeanExe.Extract.Values`
- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 16 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.depthAliasRun --out .lake/build/wasi-programs/depthAliasRun.final.wasm`
- [x] `timeout 5s build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/depthAliasRun.final.wasm < /dev/null` returned `0 1 12 6 0`.
- [x] `printf x | timeout 5s build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/depthAliasRun.final.wasm` returned `0 0 1 100 6`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/ownership_report.js` returned `checked 8 ownership report cases`.
- [x] `node test/core_correctness.js` returned `checked 784 accepted, 34 rejected, and 13 trapped cases`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 16 --module PmobOrderBook.LeanExeDepthRenderRepro --entry PmobOrderBook.LeanExeDepthRenderRepro.run --out .lake/build/repro-depth-old-state.fixed.wasm`, followed by empty stdin and stdin `x` Wasmtime runs, returned `0 1 12 6 0` and `0 0 1 100 6`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm ownership-report --module PmobOrderBook.LeanExeDepthRenderRepro --entry PmobOrderBook.LeanExeDepthRenderRepro.run` showed `PmobOrderBook.LeanExeDepthRenderRepro.oldDepth` with `compiler statement releases: none`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module PmobOrderBook.RawCommand --entry PmobOrderBook.RawCommand.run --out .lake/build/pmob-orderbook-raw.wasm`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/KernelTest.lean`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/RawCommandTest.lean`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/LeanExeDepthRenderReproTest.lean`
- [x] In `orderbook-wasm`, `go test -count=1 ./harness` returned `ok  	leanclob/orderbookwasm/harness	5.232s`.

## 2026-06-16: Type-Class Specialization Through List Helpers

Type-class evidence specialization now feeds the expression-level structural-recursion discovery pass.  When a same-root helper call has static class evidence and concrete supported runtime arguments, the discovery pass inline-specializes the helper body, normalizes class evidence, and collects any structural-recursion helpers exposed by the specialized body.  This lets generic class-constrained helpers compile when their specialized bodies call `List.foldl` or `List.find?` over supported element layouts.

The new correctness examples use `TypeclassScore` over `List (Option UInt64)`.  `typeclassScoreListFoldlDemo` folds scores through `List.foldl`, and `typeclassScoreListFindDemo` searches with `List.find?` before scoring the returned value.  Direct `List.any` remains covered by existing closed-predicate tests, but the generic class-constrained `List.any` shape still needs a predicate-extraction improvement.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/report_classification.js`
- [x] `node test/run_all.js` returned `checked 114 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 784 accepted, 34 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 298 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Type-Class Boundary Hardening

Type-class diagnostics now distinguish public runtime evidence from internal evidence-bearing helpers.  Public entries with unresolved class evidence or explicit dictionary parameters reject with `runtime class evidence is not supported`, while the report command describes internal class methods, instances, and class constructors as static-specialization requirements.  The report remains entry-aware, so accepted concrete wrappers can mention class declarations in their dependency graph without marking the whole reachable graph as rejected.

Evidence normalization now runs at class-method application sites that reach extraction after specialization, which lets source-defined class methods compile inside additional direct-lambda array callbacks.  The correctness examples now compare `TypeclassScore` methods inside `Array.any` and `Array.find?`, in addition to the earlier `Array.foldl` case.  The BEq path keeps custom lambda instances on the normalization path, but it preserves the existing structural equality lowering for evidence that is structurally derived or built from `instBEqOfDecidableEq`, including `Option.instBEq` and `Array.instBEq`.

This pass also filled direct fixed-width primitive gaps exposed by the stricter evidence handling.  Direct `UInt64`, `UInt32`, and `UInt8` comparison methods lower as conditions, direct `UInt64`, `UInt32`, and `UInt8` complement methods lower without relying on class projection unfolding, and direct `UInt8.land`, `UInt8.lor`, and `UInt8.xor` now share the existing fixed-width bitwise lowering.  Numeric class projections already handled by primitive extraction stay on that explicit path instead of being unfolded through library instance bodies.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm`
- [x] `lake build LeanExe.Extract.Report lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/report_classification.js`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayAnyDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayAnyDemo`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayFindDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayFindDemo`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectTypeclassEntry --out .lake/build/typeclass-reject-entry.wasm` rejected with `runtime class evidence is not supported: LeanExe.Examples.Correctness.rejectTypeclassEntry`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectTypeclassRuntimeDictionaryParam --out .lake/build/typeclass-reject-dict.wasm` rejected with `runtime class evidence is not supported: LeanExe.Examples.Correctness.rejectTypeclassRuntimeDictionaryParam`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 296 standard Lean comparison cases`.
- [x] `node test/core_correctness.js` returned `checked 782 accepted, 34 rejected, and 13 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/report_classification.js` returned `checked 113 report classification cases`.
- [x] `node test/run_all.js` returned `checked 113 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 782 accepted, 34 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 296 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Static Type-Class Evidence

LeanExe now treats class evidence as a static specialization input for inline-specialized helpers.  The classifier reads Lean's imported class-extension entries directly instead of importing modules with `loadExts := true`, which preserves access to source-defined classes without requiring imported initializer execution in the `lean-wasm` executable.  Specialized helper bodies run through bounded evidence normalization that beta-reduces, unfolds class evidence applications, unfolds class projection functions, and reduces projections from class constructors before ordinary extraction.

The correctness examples cover `BEq`, `Inhabited`, and a source-defined `TypeclassScore` class.  The custom `BEq` example is intentionally nonstructural, so it catches the unsound path where generic `==` would ignore the selected instance and lower to structural equality.  The `TypeclassScore` examples cover scalar and structure instances, a dependent `Option` instance, and a class method used inside an `Array.foldl` direct lambda.  Runtime dictionaries, exported unresolved class constraints, dynamic dispatch, and unsupported method result types remain outside the accepted subset.

The implementation also adds direct lowering for `UInt64`, `UInt32`, and `UInt8` arithmetic primitives exposed after method inlining, plus proof-erased lowering for `UInt64.ofNatLT`, `UInt32.ofNatLT`, and `UInt8.ofNatLT`.  Those forms are not type-class-specific; they are ordinary checked Lean fixed-width integer operations that became visible once evidence normalization exposed method bodies.  The `ofNatLT` match uses plain `Name` values because quoting the external declaration in the compiled extractor made the native `lean-wasm` executable look for a nonexistent runtime implementation of that checked constructor.

Checks run:

- [x] `lake build LeanExe.Extract.Types LeanExe.Extract.Core lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassSameUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassSameUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassSameCustomBEq --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassSameCustomBEq`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassDefaultUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassDefaultUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassDefaultPoint --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassDefaultPoint`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScorePoint --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScorePoint`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreOptionUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreOptionUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayTotalDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayTotalDemo`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 294 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 780 accepted, 32 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 294 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Type-Class Implementation Plan

`typeclasses.md` records the literature context and implementation plan for type-class support.  The design conclusion is static evidence specialization: Lean should perform instance search, and LeanExe should specialize the elaborated evidence terms until class methods become ordinary first-order code or reject the program.  Runtime dictionaries, witness tables, indirect calls, and a public ABI for class evidence remain outside the first implementation slice.

The plan is staged around evidence classification, bounded evidence normalization, specialization keys for static arguments, method lowering after specialization, comparison tests against standard Lean, and documentation updates.  The first accepted examples should cover `BEq`, `Inhabited`, and a source-defined class with dependent instances.  Rejection tests should cover exported unresolved class constraints, escaping dictionary values, unsupported method result types, and evidence normalization that fails to reach first-order code.

## 2026-05-22: Tagged List Fold Accumulators

Specialized inline calls now beta-reduce instantiated dependent domains and result types before classifying them.  This fixes generated match helpers whose declared result is `motive acc item`: after substituting a direct motive lambda, the result is an ordinary supported value type, but the previous classifier inspected the unreduced application and rejected the helper as an unsupported function type.

The standard comparison corpus now accepts closed `List.foldl` examples whose accumulators are heap-bearing tagged values.  The new cases cover `Option ByteArray` and `Except ByteArray ByteArray` accumulators over list elements that also contain heap-bearing tags, and both cases compare generated WASM under Wasmtime with the standard Lean toolchain.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure-bytes --module LeanExe.Examples.Correctness --entry optionByteArrayListFoldlTaggedAccumulatorValue --serializer 'LeanExe.Examples.Correctness.optionByteArrayBytes __leanexeValue'` returned `matched pure-bytes LeanExe.Examples.Correctness.optionByteArrayListFoldlTaggedAccumulatorValue`.
- [x] `node tools/compare-standard.js --mode pure-bytes --module LeanExe.Examples.Correctness --entry exceptByteArrayUInt64ListFoldlTaggedAccumulatorValue --serializer 'LeanExe.Examples.Correctness.exceptByteArrayByteArrayBytes __leanexeValue'` returned `matched pure-bytes LeanExe.Examples.Correctness.exceptByteArrayUInt64ListFoldlTaggedAccumulatorValue`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 286 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 772 accepted, 32 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 286 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Bearing List Fold Comparisons

The standard comparison corpus now covers heap-bearing `List.foldl` and `List.foldr` results over `List (Option ByteArray)` and `List (Except ByteArray UInt64)`.  The accepted cases return `ByteArray` values directly and return a `ByteOutputState` structure that carries a byte-array accumulator.  The corpus also records direct `List.concat` as accepted after verifying the generated WASM against standard Lean with the appended element demanded by a structural sum.

The new rejection cases marked the then-current boundary around closed structural folds.  Local callback values, function-valued accumulators, nested closed folds, and a tagged `Option ByteArray` accumulator that lowered through an unsupported generated matcher were outside the accepted subset at this checkpoint.  The 2026-05-22 entry supersedes the tagged-accumulator part of that boundary.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 284 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 772 accepted, 33 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 284 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Tagged List Predicates

The standard comparison corpus now covers direct `List.any` and `List.all` over non-scalar element layouts.  The new cases exercise structures, source-defined tagged values, `ByteArray`, `Option UInt64`, `Option ByteArray`, and `Except ByteArray UInt64`, comparing standard Lean execution with generated WASM under Wasmtime.

The recursive-family specialization also now has heap-bearing tagged list-result cases.  `List (Option ByteArray)` and `List (Except ByteArray UInt64)` are tested through `List.map`, `List.filter`, `List.find?`, and append after reverse with source-level byte serializers.  One serializer alias had to be eta-expanded because the extractor accepts ordinary function bodies at that boundary, not a bare definition alias.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 277 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 277 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Non-Scalar List Comparisons

The standard comparison corpus now covers monomorphic `List` values whose elements are structures, source-defined tagged values, byte arrays, and nested `Option` values.  The new fixtures exercise `List.map`, `List.filter`, `List.find?`, append after reverse, `List.foldl`, and `List.foldr`, comparing standard Lean execution with generated WASM under Wasmtime through byte serializers or scalar slots.  This extends the tested recursive-family specialization beyond `List UInt64` without adding a list-specific compiler path.

The first `List (Option UInt64).find?` case exposed a missing condition-extraction branch for generated `Option` matchers.  Value extraction already accepted that matcher form, but condition extraction skipped from generated `Except` matches to `Nat` matches.  The extractor now routes generated `Option` matchers used as conditions through the ordinary value extractor before converting the scalar result to a condition.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure-bytes --module LeanExe.Examples.Correctness --entry optionUInt64ListFindValue --serializer 'LeanExe.Examples.Correctness.optionOptionUInt64Bytes __leanexeValue'` returned `matched pure-bytes LeanExe.Examples.Correctness.optionUInt64ListFindValue`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 257 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 257 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Recursive Flow Comparisons

The standard comparison corpus now covers recursive `U64Binary` values flowing through ordinary first-order program shapes.  The new fixtures compare `Option.map`, `Except.map`, `Except.bind`, branch-selected structures with recursive fields, source-defined tagged values with recursive payloads, arrays of recursive values, and `Id.run` loops carrying recursive, `Option` recursive, and `Except ByteArray` recursive state.  These tests compare standard Lean execution with generated WASM under Wasmtime through byte serializers, so the checked behavior is the source-level value rather than a hand-written numeric summary.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 233 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 233 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Conservative Recursive Cleanup

Recursive result cleanup now follows the project policy that leaks are acceptable and incorrect computation is not.  The result-materialization cleanup pass no longer emits compiler releases for ordinary recursive heap temporaries in scalar-result functions or heap-result functions.  It still releases nonrecursive owners such as `ByteArray` and `Array` when the existing local rules prove them fresh and absent from returned roots.

The aliasing corpus now includes source programs that share recursive children through constructor fields, return a subtree alias, duplicate recursive values in an array, duplicate recursive fields in a structure, and duplicate recursive payloads in a tagged value.  These cases compare the generated WASM under Wasmtime with standard Lean execution where possible.  The first version of the tests exposed unsafe compiler-inserted recursive releases in scalar-result functions, which now report no compiler statement releases in `ownership-report`.

Checks run:

- [x] `lake build LeanExe.Extract.Values LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm ownership-report --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64BinarySharedChildScore` reported `compiler statement releases: none`.
- [x] `.lake/build/bin/lean-wasm ownership-report --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64BinaryReturnedSubtreeAliasScore` reported `compiler statement releases: none`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check tools/compare-standard.js`
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 771 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 217 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 217 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap Owner Provenance

Owned-mask generation now tracks the local slot that first received an owned heap value.  When a later heap or array allocation consumes child slots, the compiler transfers ownership for only the first use of a source slot and retains later aliases.  Result materialization also refreshes owned masks after pruning local lets, so sequential source `let` bindings keep the ordered ownership context that extraction created.

`sharedRecursiveChildReleaseStats` covers the duplicate-reference case with a recursive binary tree.  The program constructs one leaf, stores that same leaf in both fields of a node, releases the node, and returns a packed counter value.  The expected `10302` means one retain during construction, three release calls during teardown, and two freed heap objects.

Checks run:

- [x] `lake build LeanExe.Extract.Values`
- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.sharedRecursiveChildReleaseStats --out .lake/build/shared-recursive-child-release.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke sharedRecursiveChildReleaseStats .lake/build/shared-recursive-child-release.wasm` returned `10302`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 766 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 766 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 212 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Release Alias Propagation

A recursive value returned from a helper function trapped when source code released it with `LeanExe.Runtime.release`.  The helper result lived in local `2`, result materialization copied it into local `3`, and the source release consumed local `3`.  Release analysis propagated aliases inside a local-let prefix, but it did not propagate a release from the following body back into the prefix, so local `2` remained eligible for an automatic compiler release.

Release accounting now tracks release targets through `let` aliases and local-let prefixes using the set of slots released later in the expression or value.  A body release of an alias now marks the owner slot that produced the alias, while call-result ownership still treats returned slots as owned results rather than as ownership of the call arguments.  `recursiveScenarioHelperRuntimeReleaseStats` covers the helper-return case for leaf, balanced, and skewed recursive trees, and the ownership report asserts that the compiler emits no extra release for the helper result.

Checks run:

- [x] `lake build LeanExe.Extract.Values LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm ownership-report --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveScenarioHelperRuntimeReleaseStats` reported `compiler statement releases: none`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveScenarioHelperRuntimeReleaseStats --out .lake/build/recursive-helper-release.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveScenarioHelperRuntimeReleaseStats .lake/build/recursive-helper-release.wasm 0` returned `101`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveScenarioHelperRuntimeReleaseStats .lake/build/recursive-helper-release.wasm 1` returned `707`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveScenarioHelperRuntimeReleaseStats .lake/build/recursive-helper-release.wasm 2` returned `707`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node --check test/ownership_report.js`
- [x] `node test/ownership_report.js` returned `checked 8 ownership report cases`.
- [x] `node test/refcount.js` returned `checked 37 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 765 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 765 accepted, 29 rejected, and 13 trapped cases`, `checked 37 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 212 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Recursive Standard Comparisons

The standard comparison self-test now has parameterized recursive-value fixtures.  `leanListScenarioScore` compares empty, singleton, ordinary, and longer `List UInt64` inputs through scalar summaries, while `leanListScenarioReverseValue` and `leanListScenarioAppendMapValue` return recursive values that the wrapper serializes through the existing list renderer.  `u64BinaryScenarioScore` compares leaf, balanced, and skewed binary-tree shapes through scalar summaries, while `u64BinaryScenarioValue`, `u64BinaryScenarioMirrorValue`, `u64BinaryScenarioFindValue`, and `u64BinaryScenarioRequireByteErrorValue` compare returned recursive values, present and missing searches, and `Except ByteArray U64Binary` success and error paths.

Release-counter checks remain in the Wasmtime correctness and refcount suites because standard Lean defines `LeanExe.Runtime` counters as zero.  `recursiveScenarioRuntimeReleaseStats` now checks explicit source-level release of leaf, balanced, and skewed recursive trees, with the refcount suite asserting one released block for a leaf and seven released blocks for the nontrivial trees.  During exploratory testing, releasing a recursive value returned from a helper function trapped; that pattern needs a root-cause pass before it becomes a supported release-counter fixture.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node test/core_correctness.js` returned `checked 762 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/refcount.js` returned `checked 34 refcount cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 212 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 762 accepted, 29 rejected, and 13 trapped cases`, `checked 34 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 212 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Standard Comparison Edge Cases

The standard comparison self-test now covers more of the scalar and tagged-value perimeter against official Lean execution.  The added cases compare short-circuiting, fixed-width division by zero, UInt64 wrapping, Nat subtraction and division edge cases, fixed-width UInt8 and UInt32 wrapping, Option and Except public layouts, array reads, array filters, fixed-width array element operations, and selected foldr windows.  Pure comparison mode now normalizes successful Wasmtime `i64` CLI output back to unsigned `UInt64` text, because the harness slot type is `Array UInt64` while Wasmtime renders high-bit `i64` results as signed decimal.

The public ABI comparison slice now includes heap-bearing tagged argument values in addition to previous heap-bearing results.  It covers `Option (Array ByteArray)`, `Except ByteArray (Array ByteArray)`, `Array (Option ByteArray)`, `Array (Except ByteArray ByteArray)`, and `Option (Array (Option ByteArray))`, with both present and absent or error and ok constructor paths where those paths have different semantics.  These cases still compare standard Lean output with generated WASM executed under Wasmtime.

Checks run:

- [x] `node --check tools/compare-standard.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 189 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 751 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 189 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: More Standard Comparison Cases

The standard comparison self-test now includes repeated inputs for several programs rather than one representative call per entry.  The added cases cover pure scalar entries with different arguments, public nested-array and byte-array-array ABI arguments, byte-array stdin transforms on empty and nonempty input, JSON GCD success and error inputs, typed JSON object decoding success and schema-error inputs, JSON addition with reordered fields and overflow, Collatz JSON success and error inputs, and argv success and error behavior.  Each case still runs the official Lean program and compares it with the LeanExe-generated WASM under Wasmtime.

Checks run:

- [x] `node --check tools/compare-standard.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 126 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 751 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 126 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Array foldr

`Array.foldr` now lowers through the array multi-slot fold IR with an explicit traversal direction.  The reverse loop evaluates the array, `start`, `stop`, and initial accumulator once, clamps `start` to the array size, decrements before each load, and treats `stop` as the exclusive lower bound.  The direct-lambda body follows Lean's `α -> β -> β` binder order, while sharing the staged accumulator assignment and heap-accumulator release rule used by `Array.foldl`.

The correctness corpus covers the default scan, explicit windows, clamped starts, skipped empty bodies, structured accumulators, byte-array accumulators, and release counters.  Standard comparison checks both a scalar `foldr` result and a byte-array `foldr` result against the official Lean toolchain.  The specification, manual, README, and plan now describe `Array.foldr` as part of the supported fixed-width array surface, with attached-array erasure still limited to `foldl` and `foldlM`.

Checks run:

- [x] `lake build LeanExe.IR.Core LeanExe.Extract.Core LeanExe.Wasm.Binary LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldrDigits --out /tmp/arrayFoldrDigits.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldrDigits /tmp/arrayFoldrDigits.wasm` returned `321`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldrByteArrayAccumulatorReleaseStats --out /tmp/arrayFoldrByteArrayAccumulatorReleaseStats.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldrByteArrayAccumulatorReleaseStats /tmp/arrayFoldrByteArrayAccumulatorReleaseStats.wasm` returned `30202`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check tools/compare-standard.js`
- [x] `node test/core_correctness.js` returned `checked 751 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 105 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 751 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 105 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Pure-ABI Parameter Comparisons

The standard comparison self-test now covers `pure-abi` library calls with heap-backed public parameters as well as heap-backed public results.  The added cases materialize nested scalar arrays, arrays of byte arrays, arrays of tagged values with byte-array payloads, and arrays of structures whose fields contain nested byte-array arrays through the Wasmtime C host script path.  A small `publicNestedArrayOpsReturn` correctness fixture gives `Array (Array UInt64)` a parameter-to-result case, matching the existing byte-array, tagged, and structured array examples.

The command-line path now has documented and tested `--abi-arg` coverage.  The standard Lean side receives an explicit `--standard-call`, while the generated WASM side receives the JSON-described ABI argument through the host runner and decodes the returned public ABI value from result slots plus targeted memory reads.

Checks run:

- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node tools/compare-standard.js --self-test` returned `checked 103 standard Lean comparison cases`.
- [x] `node tools/compare-standard.js --mode pure-abi --module LeanExe.Examples.Correctness --entry publicByteArrayArrayOpsReturn --abi-layout '{"array":"ByteArray"}' --abi-arg '{"layout":{"array":"ByteArray"},"value":[[65],[66,67],[68,69,70]]}' --standard-call 'LeanExe.Examples.Correctness.publicByteArrayArrayOpsReturn #["A".toUTF8, "BC".toUTF8, "DEF".toUTF8]' --serializer '__leanexeJsonArray __leanexeValue __leanexeJsonByteArray'` returned `matched pure-abi LeanExe.Examples.Correctness.publicByteArrayArrayOpsReturn`.
- [x] `node test/core_correctness.js` returned `checked 744 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 744 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 103 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Standard Comparison for Public ABI Values

`tools/abi_layout.js` now owns the public ABI layout helpers that used to live inside `test/core_correctness.js`.  The shared code can materialize scalar, byte-array, array, structure, and tagged public arguments for the Wasmtime C host script runner, plan targeted memory reads for heap-backed results, decode those sparse memory reads back to JavaScript values, and compare nested ABI values structurally.

`tools/compare-standard.js` now has `pure-abi` mode for library exports whose public results contain heap-backed ABI values.  Standard Lean still computes the expected value, but the runner serializes that value to JSON through the caller's `--serializer`; the generated WASM is executed through the Wasmtime C host, and the result is decoded from ABI slots plus targeted memory ranges.  This adds standard Lean comparisons for public structure results with array fields, public `Array ByteArray`, public arrays of tagged values, and public arrays of structures with nested arrays.

Checks run:

- [x] `node --check tools/abi_layout.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check tools/compare-standard.js`
- [x] `node tools/compare-standard.js --mode pure-abi --module LeanExe.Examples.Correctness --entry publicByteArrayArrayReturn --abi-layout '{"array":"ByteArray"}' --serializer '__leanexeJsonArray __leanexeValue __leanexeJsonByteArray'` returned `matched pure-abi LeanExe.Examples.Correctness.publicByteArrayArrayReturn`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 98 standard Lean comparison cases`.
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 98 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Wasmtime Setup and Targeted Reads

`tools/download-wasmtime.sh` now downloads the Wasmtime CLI and matching C API archive into `build/tools/wasmtime`, using Wasmtime 44.0.0 and the detected Linux platform by default.  `tools/build-wasmtime-host.sh` derives the same version and platform, and still accepts `WASMTIME_C_API` for a custom C API package.  The repository-local Wasmtime setup is now reproducible from tracked tooling.

The C host script mode no longer dumps the full WASM memory for ABI assertions.  It keeps the Wasmtime instance alive after the call, supports `read-u64` and `read-memory` commands that can refer to result slots and earlier reads, and exits through an explicit `done` command.  `test/core_correctness.js` now plans the memory ranges required by each expected heap result and checks those ranges through a sparse memory reader.

Checks run:

- [x] `tools/download-wasmtime.sh`
- [x] `tools/build-wasmtime-host.sh`
- [x] `node --check test/wasmtime_host.js`
- [x] `node --check test/core_correctness.js`
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/no_js_wasm_execution.js` returned `checked JavaScript WASM execution guard`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Wasmtime Host Runner

The test suite now has a small C host runner built against the Wasmtime C API.  The runner instantiates a compiled library-mode module with Wasmtime, materializes `i64` and `ByteArray` arguments through the module's exported `alloc`, calls one exported function, and prints either an `i64`, flattened result slots, or returned bytes as hex.  This removes JavaScript WASM execution from the byte-array allocation tests, ASCII-string tests, JSON byte-transform tests, and validator fuzz test while preserving host-memory argument and result coverage for those cases.

The matching Wasmtime C API package for the existing CLI version is expected at `build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux-c-api`, or through `WASMTIME_C_API`.  `tools/build-wasmtime-host.sh` builds `build/tools/leanexe-wasmtime-host` from `tools/wasmtime-host.c`.  Node still orchestrates tests, but it no longer instantiates or executes WASM.

The runner now also owns the same-instance reference-count checks that used to require JavaScript's embedded engine.  Its dedicated commands cover release reuse, retained-pointer delayed reuse, the `free` alias, allocator growth, reset-sensitive temporary reuse for byte-array and array inputs, no-argument temporary reuse, and scalar calls with `Array UInt64` and `ByteArray` arguments.  A script mode lets `test/core_correctness.js` construct arbitrary public ABI inputs through symbolic `alloc`, byte writes, slot writes, and argument commands, then receive flattened result slots and targeted memory ranges for ABI assertions.  `test/no_js_wasm_execution.js` now fails the suite if test or tool JavaScript reintroduces direct WASM execution references.

Checks run:

- [x] `tools/build-wasmtime-host.sh`
- [x] `node --check test/wasmtime_host.js`
- [x] `node --check test/bytearray_alloc.js`
- [x] `node --check test/asciistring.js`
- [x] `node --check test/json_double.js`
- [x] `node --check test/fuzz_validate.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/no_js_wasm_execution.js`
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/asciistring.js` returned `checked 23 asciistring cases`.
- [x] `node test/json_double.js` returned `checked 48 json program cases`.
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 10` returned `checked 16 cases`.
- [x] `node test/refcount.js` returned `checked 31 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/no_js_wasm_execution.js` returned `checked JavaScript WASM execution guard`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Bearing Array Ownership Tests

The correctness corpus now measures release behavior for arrays whose elements contain heap references through `Option ByteArray`, `PublicToken`, and `ByteArrayGroup`.  The refcount tests assert that source-level `Runtime.release` frees child values through the generic element layout, and the fold accumulator tests assert that array folds release replaced heap-bearing accumulators.  Public ABI rejection coverage now includes recursive values hidden inside `Option (Array U64List)`, a structure, and a tagged wrapper, so recursive public roots remain excluded even through otherwise supported containers.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node --check test/ownership_report.js`
- [x] `node test/ownership_report.js` returned `checked 7 ownership report cases`.
- [x] `node test/refcount.js` returned `checked 31 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Bearing Array Operations

The correctness corpus now exercises ordinary array operations over fixed-width heap-bearing element layouts.  The new entries cover `Array (Option ByteArray)`, `Array (Except ByteArray ByteArray)`, `Array PublicToken`, and `Array ByteArrayGroup`, where `ByteArrayGroup` contains an `Array ByteArray` field.  The exercised operations include public parameter materialization, public result decoding, `push`, append notation, `extract`, `setIfInBounds`, `insertIdxIfInBounds`, `eraseIdxIfInBounds`, `swapIfInBounds`, `reverse`, `map`, `filter`, `find?`, `findIdx?`, `any`, `all`, `foldlM`, and structural equality for arrays whose elements contain byte arrays or nested arrays.

No compiler change was required.  These tests verify that the fixed-width layout, child-owner masks, retained copied children, inactive tagged payload slots, and public ABI reader/writer helpers compose for the heap-bearing element layouts already accepted by the compiler.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 737 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 112 report classification cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 4 ownership report cases`, `checked 737 accepted, 25 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Public Tagged Heap Arrays

The public ABI coverage now includes heap-bearing arrays inside supported structures, nonrecursive tagged values, `Option`, and `Except`.  The correctness fixture covers public `Option (Array ByteArray)`, `Except ByteArray (Array ByteArray)`, arrays of `Option ByteArray`, arrays of `Except ByteArray ByteArray`, arrays of a source-defined `PublicToken` tag containing `ByteArray`, a public structure carrying `Array ByteArray`, and a public tagged result whose ok constructor carries `Array ByteArray`.  It also exercises `Array ByteArray` update, append, extract, insert, erase, swap, reverse, map, filter, find, any, all, and `foldlM` operations through public parameters and results.

The JS correctness harness now has composable ABI layout helpers for scalar slots, byte arrays, arrays, structures, and tagged values.  Tests can materialize nested public arguments and read nested public results through the same layout description, so future public ABI cases should not need one-off memory readers.  The old dedicated readers for public byte-array arrays, nested scalar arrays, and arrays of specific structures were removed from the active path.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check test/core_correctness.js`
- [x] `node test/core_correctness.js` returned `checked 722 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 105 report classification cases`.
- [x] `node test/run_all.js` returned `checked 105 report classification cases`, `checked 4 ownership report cases`, `checked 722 accepted, 25 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Public Heap-Bearing Arrays

The public array ABI now accepts fixed-width element layouts that contain heap-reference fields.  `Array ByteArray`, nested arrays such as `Array (Array UInt64)`, arrays of structures containing `ByteArray`, and arrays of structures containing array fields can appear as entry parameters and entry results.  The public element predicate is separate from the internal element predicate: it permits scalar values, `ByteArray`, nested arrays, structures, nonrecursive inductives, `Option`, and `Except` when all flattened fields meet the same rule, while recursive inductive values remain excluded from the public ABI.

The boundary representation uses the same slots as internal arrays.  `ByteArray` elements use owner, pointer, and length slots; nested arrays use owner and pointer slots.  Host-provided borrowed children use owner `0`, and compiler-owned result arrays retain the existing child-pointer mask behavior so `release` can reclaim owned byte arrays and nested arrays reached from an array result.

Checks run:

- [x] `lake build LeanExe.Extract.Types LeanExe.Extract.Values LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/report_classification.js` returned `checked 97 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 703 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 97 report classification cases`, `checked 4 ownership report cases`, `checked 703 accepted, 25 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Atomic Multi-Slot Fold Pruning

The liveness pass now treats a materialized multi-slot fold result as an atomic local assignment.  Before this change, a let-bound `Except UInt64 ByteArray` or `Option ByteOutputState` loop result could be pruned down to the tag and one scalar payload field when the later `match` ignored the byte-array payload.  That split one fold result into separate result-slot expressions, so the generated code ran the loop more than once and duplicated accumulator releases.

The pruning rule now keeps the complete `.slots` local let whenever `foldMultiSlotAssign?` recognizes the values as one fold assignment and any target slot remains live.  The ordinary scalar-slot pruning path still applies to unrelated `.slots` lets.  The counter examples now report the intended two loop-replacement releases and two frees: `exceptForByteArrayOutputReleaseStats` returns `10202`, and `optionForByteArrayStateReleaseStats` returns `30202`.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/ownership_report.js` returned `checked 4 ownership report cases`.
- [x] `node test/core_correctness.js` returned `checked 695 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 4 ownership report cases`, `checked 695 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Ownership Report Command

`lean-wasm ownership-report --module M --entry E` now compiles the selected entry through the same two-pass extraction path as `compile`, then reports ownership data from the extracted IR.  The command lists each extracted function's result type, internal result owner offsets, helper-result fresh-owner offsets, returned owner expressions, compiler-emitted statement releases, fold accumulator release offsets, and explicit `LeanExe.Runtime.release` expressions.  `compileEnvironmentWithEntryModeDetailed` exposes the extraction context and IR together, while the existing compile entry points keep returning the same `IRModule` type.

The first tests cover the `Option ByteArray` and `Except UInt64 ByteArray` loop-output counter examples and `JsonTreeCommand.makeTree`.  The initial structured `Except` report showed two byte-array fold result slots with the same accumulator release offset, which identified the duplicate result-demand issue fixed in the next ownership change.  The report also distinguishes the source-level release in `JsonTreeCommand.insertOwned` from compiler-emitted releases, so source ownership boundaries and automatic cleanup can be inspected separately.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/ownership_report.js` returned `checked 3 ownership report cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 3 ownership report cases`, `checked 695 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Option and Except foldlM

`Array.foldlM` and `ByteArray.foldlM` now compile for `Option` and `Except ε` when the callback is a direct lambda and the accumulator payload has a supported concrete layout.  The extractor represents the loop accumulator as the monad result value, stages each callback result through the existing multi-slot fold loop, and derives the loop stop flag from the staged tag.  A `none` or `Except.error` result stops the generated loop before later callback bodies run.

This uses the existing `Array.foldl` and `ByteArray.foldl` machinery instead of adding a new IR loop.  The implementation accepts the same accumulator payload classes as ordinary folds, including byte arrays and supported structures, while keeping `Id` `foldlM`, effectful callbacks, and escaping callback values rejected.  The correctness examples cover success, early failure that skips a later trap, an `Option ByteArray` accumulator, and `Array.attach.foldlM` with erased membership proofs.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 680 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 84 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 680 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 84 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Interleaved Inline Specialization

Transparent inline specialization now supports static type, proof, and direct-lambda arguments interleaved with runtime arguments.  The specializer walks the helper lambda prefix in source order, substitutes static binders in place, preserves runtime binders in order, and lifts substituted static expressions across preserved runtime binders.  Inline extraction now appends the caller locals after helper runtime argument bindings, so a substituted direct lambda can capture a caller-local value without turning into a runtime closure.

Dependency collection now follows inline-only helper bodies far enough to add their supported callees to the compiled function set.  The inline-only helper itself remains uncompiled and specialized at the call site.  This fixes helper shapes such as `decodeRequiredField fields name (fun raw => ...)`, where the supported callees live inside a helper whose own type contains a function parameter.

The correctness corpus now includes `genericInterleavedLambdaHelper`, which calls a polymorphic helper with runtime arguments before a direct lambda that captures a local `bonus`.  The JSON decoder layer now includes `decodeRequiredField`, and `JsonObjectArrayDecode` uses it for scalar fields and for the nested `decodeArray` item decoder.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm LeanExe.Examples.Correctness LeanExe.Examples.JsonObjectArrayDecode` returned successfully.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.genericInterleavedLambdaHelper --out .lake/build/generic-interleaved.wasm` returned successfully.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke genericInterleavedLambdaHelper .lake/build/generic-interleaved.wasm` returned `22`.
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonObjectArrayDecode --entry LeanExe.Examples.JsonObjectArrayDecode.transform --out .lake/build/json-object-array-decode.wasm` returned successfully.
- [x] `printf '%s' '{"items":[{"id":1,"weight":4},{"id":2,"weight":7}],"scale":3}' | build/tools/wasmtime/current/wasmtime run .lake/build/json-object-array-decode.wasm` returned `{"weighted":54,"count":2}`.
- [x] `node test/core_correctness.js` returned `checked 670 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 79 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 670 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 79 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: JSON Object Array Decoding

The JSON decoder layer now has a generic `decodeArray` helper that accepts a direct decoder lambda and returns an array of decoded source-level values.  This required two compiler generalizations: transparent inline specialization now accepts direct-lambda static arguments before runtime arguments, and generated `Except` match helpers are recognized by locating the typed `Except` scrutinee even when Lean places type and motive parameters before it.  The lambda is substituted into the helper body, so the generated WASM still contains first-order code rather than a runtime closure.

`LeanExe.Examples.JsonObjectArrayDecode` decodes `{"items":[{"id":...,"weight":...}],"scale":...}` into source-defined `Item` and `Request` structures, rejects duplicate, missing, unknown, and mistyped fields, checks arithmetic overflow, and returns `{"weighted":...,"count":...}` through the WASI `Except` adapter.  The example keeps JSON decoding as ordinary Lean code over the recursive AST.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm LeanExe.Examples.JsonObjectArrayDecode` returned successfully.
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonObjectArrayDecode --entry LeanExe.Examples.JsonObjectArrayDecode.transform --out .lake/build/json-object-array-decode.wasm` returned successfully.
- [x] `printf '%s' '{"items":[{"id":1,"weight":4},{"id":2,"weight":7}],"scale":3}' | build/tools/wasmtime/current/wasmtime run .lake/build/json-object-array-decode.wasm` returned `{"weighted":54,"count":2}`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 78 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 669 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 78 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Typed JSON Decode Helpers

The JSON AST now has a small `Except ByteArray` decoder layer in `LeanExe.Ascii.Json.Decode`.  It wraps parse, render, object lookup, required-field lookup, typed scalar assertions, exact field-set checks, and unsigned-integer array decoding without adding JSON-specific compiler behavior.  `LeanExe.Examples.JsonTypedDecode` uses that layer to decode a JSON object into a source-defined request structure, reject missing, duplicate, unknown, and mistyped fields, check arithmetic overflow, and return compact JSON through the WASI `Except` adapter.

Checks run:

- [x] `lake build LeanExe.Ascii.Json.Decode LeanExe.Examples.JsonTypedDecode` returned successfully.
- [x] `node test/wasi_program.js` returned `checked 29 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 77 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 669 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 29 WASI program cases, 2 traps, and 7 rejections`, `checked 77 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Except Do-Notation Parser Shapes

The correctness corpus now covers parser-shaped `Except` do-notation that calls helpers using accepted pure `Id.run` cursor loops.  The new examples return a structured ok payload, a nonrecursive tagged ok payload, and a byte-array ok payload, and they check that an error result skips a later trapping computation.  No extractor change was needed; the existing first-order `Except` bind lowering and pure-loop extraction already accepted these checked forms.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 669 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 76 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 669 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 76 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Sparse User-Inductive Matches

Pure `Id.run do` examples now cover sparse matches over nonrecursive user inductives.  The correctness corpus has `if let Status.ok value := status`, a named catch-all `Status` arm that rematches the fallback value, a nullary-constructor `Mode` `if let`, and a `while` loop that reads `Array Status` elements and uses the same sparse match inside the loop body.  These examples cover the source style used for tagged status values without making the compiler know about `Status`.

The matcher classifier now recognizes generated sparse match helpers whose explicit arms are indexed by constructor result types and whose fallback arm receives the whole scrutinee type.  The value extractor binds that fallback arm to the reconstructed nonrecursive tagged value for each unmatched constructor path.  Sparse generated matches over recursive inductives remain rejected.  The loop-step extractor also beta-reduces first-order local continuation lambdas before classifying let-bound types, matching the existing ordinary value extractor behavior.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 665 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 72 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 665 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 72 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Mutable Id Matches and If-let

Pure `Id.run do` examples now cover mutable assignments under `match` and `if let`.  The correctness corpus has an `Option` match that updates a scalar, an `if let some` assignment, a named catch-all `Option` arm that uses the fallback scrutinee value, a user-defined `Status` match that returns a tagged value, and a state-record update under an `Option` match.  These examples exercise the source shapes used by ordinary parser and transformer code without adding a source-level special case for parser programs.

The compiler change is in generated `Option` matcher recognition.  Lean may elaborate `if let some ...` and sparse `Option` matches to a local `match_` helper whose fallback arm receives the scrutinee rather than a unit argument.  The matcher classifier now treats an arm whose parameter has the `Option α` scrutinee type as the none/catch-all arm, and the extractor binds that parameter to an `Option.none` value on the none path.  The same binding rule is used in the restricted Nat-tail-recursion matcher path.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 661 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 68 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 661 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 68 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Heap-field Id state records

Pure `Id.run do` examples now cover mutable state records that contain heap fields.  The correctness corpus has one parser-style `while` loop that carries `pos`, `out : ByteArray`, and `ok` in one structure, stops at a nondigit, and returns the byte output accumulated before the stop.  It also has a mutable state record that carries an internal `Array UInt64` and a counter through a `while` loop, updating array elements with the current counter value.

This slice adds coverage rather than a new compiler rule.  The existing internal structure layout, byte-array owner slots, internal array owner slots, generated structure matcher extraction, and pure-loop accumulator path already provide the required behavior.  The new examples make that support observable through Wasmtime and through the standard Lean comparison harness.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 656 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 63 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 656 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 63 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Parser-Style Id Cursor Loops

Pure `Id.run do` examples now cover parser-style cursor code.  The correctness corpus has a byte scanner that reads `input[pos]!`, stops on the first non-digit, and returns a structure; a byte-output loop that writes parsed digit values; an `Except UInt64 DigitState` parser status; and a mutable `Array UInt64` updated in a `while` loop before a `for` fold.  These examples exercise indexed reads, mutable cursors, mutable heap values, mutable arrays, explicit status, and loop-exit control in one source style.

The compiler change is in generated structure matcher extraction.  Lean carries several mutable locals through loops as nested `MProd` values, then may recover the locals through a generated matcher whose arm receives flattened fields such as `ok`, `pos`, and `sum`, rather than an immediate nested pair.  Structure match extraction now checks the arm lambda arity and, when it matches the flattened field count of nested single-constructor structures, binds those flattened fields directly.  Ordinary immediate-field structure matches keep their previous behavior.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 654 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 61 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 654 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 61 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Ordinary Id Mutable Assignments

Pure `Id.run do` extraction now handles ordinary mutable-local code outside loop bodies.  Lean lowers nested assignment branches to local continuation lambdas that accept the current mutable locals and a `PUnit` sequencing value, then return an `Id` result.  The extractor now substitutes those local lambdas when they remain first-order, beta-reduces their direct applications, treats `PUnit` as the existing unit representation, and lowers `ite (Id α)` by extracting both branch values under a shared condition.

The correctness corpus now covers multiple scalar mutable locals under nested conditionals, structure return after assignment, `ByteArray` return after branch assignment, `Option` return after mutable status updates, and `Except` return after mutable status updates.  The standard Lean comparison self-test covers the same scalar, structure, tagged, and byte-array results.  The rejection corpus now includes a local function stored as data inside `Id.run`, so this change accepts Lean's generated local continuations without adding runtime closures.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 650 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 57 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 650 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 57 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Pure While and Nested Id Loops

The extractor now accepts the checked Lean form behind source `while` loops.  Lean elaborates `while` in `Id.run do` to `ForIn.forIn` over `Lean.Loop`, whose step returns `ForInStep.done` to stop and `ForInStep.yield` to continue.  The IR now has `loopFoldMultiSlot` expression and statement forms that reuse the existing multi-slot accumulator layout without inventing a source-level loop syntax in the compiler.

Loop-body extraction now has a second path for ordinary pure `Id` computations that produce a `ForInStep` value.  The older parser still handles direct `yield`, `done`, `break`, `continue`, and simple conditional step shapes.  When the body contains nested pure loops or generated product and structure destructuring, the extractor materializes the `ForInStep` value once, reads its tag, selects the active accumulator payload, and carries the done flag through the same staged loop assignment path.

The correctness corpus now covers multiple mutable locals in a `for` loop, nested array `for` loops, scalar `while`, `while` with `break` and `continue`, a structure accumulator in `while`, nested `while`, and a byte-array result built in `while`.  The standard Lean comparison self-test covers the nested array loop, `while` with `break` and `continue`, and the byte-array `while` result.  This moves ordinary cursor and counter code closer to the intended first-order programming style while keeping the source language pure.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Wasm.Binary` returned successfully.
- [x] `lake build LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 645 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 52 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 645 accepted, 29 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 52 standard Lean comparison cases`, and `checked 56 cases`.

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
- [x] Node WebAssembly execution checks returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

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

## 2026-05-20: Monadic loops

The extractor now carries the selected `ForIn.forIn` monad through the existing checked-loop lowering.  `Id` loops use the previous `ForInStep` body extraction, while `Option` and `Except ε` loops carry the accumulator as `Option α` or `Except ε α`, unwrap the successful payload for the body, and stop after `none`, `Except.error`, or `ForInStep.done`.  The implementation follows Lean's checked term for `for`, `while`, `break`, and `continue`, so those source forms share one lowering path.

The correctness corpus covers `Except` loops over fixed-width arrays, `Option` loops over `ByteArray`, `Except` range loops with `break`, `Option` array loops with `continue`, and an `Option` source `while` loop through `Lean.Loop`.  The standard comparison harness now checks representative monadic-loop entries against the official Lean toolchain.  `spec.md`, `manual.md`, `README.md`, and `plan.md` describe loops in `Id`, `Option`, and `Except` as the accepted surface when the collection and accumulator layouts are supported.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 687 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 89 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 687 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 89 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Heap-valued monadic loop accumulators

The monadic loop tests now cover `Option` and `Except` loops whose accumulator is a `ByteArray` or a structure containing a `ByteArray`.  These cases exercise the ownership path where each iteration constructs a fresh heap value and replaces the previous accumulator.  The extractor now reduces constant IR conditions through simple local lets, tracks constants through local-let ownership analysis, and recognizes constant-source monadic binds before choosing the generic bind lowering.  Heap-valued bind sources use the materialized path so the continuation receives stable local slots instead of re-demanding separate fields of a heap result.

The release-counter examples originally showed the remaining ownership issue after this slice.  `Option ByteArray` reported the intended two loop-replacement releases for a three-byte output, while `Except UInt64 ByteArray` and `Option ByteOutputState` exposed duplicate demand in their stat examples.  The later atomic multi-slot fold pruning change fixes that demand issue by preserving one materialized fold assignment when only part of a tagged or structured result is live.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 695 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 94 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 695 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

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

## 2026-06-19: Talos association-list example

`LeanExe.Examples.TalosAssocList` defines an ordinary Lean association-list lookup over `List (UInt64 × UInt64)`.  The exported `lookupDemo` function takes a `UInt64` key, searches a fixed source-level list of pairs, returns the first matching value, and returns `0` for a miss.  This keeps recursive data internal while exercising product element layout, source-level product destructuring in a list constructor arm, and direct structural recursion through the generated list matcher.

The compiler change belongs in structural-recursion arm binding, not in `List` or association-list recognition.  Lean elaborates a source pattern such as `(k, v) :: rest` into separate lambdas for the pair fields before the recursive tail, while the constructor field layout remains one product value.  `consumeStructuralArmBinders` now expands an expected product runtime binder into projected field binders when the arm lambda destructures the product, preserving the previous single-binder path when the source keeps the product intact.

The Talos artifact decodes the generated WASM for `lookupDemo` and proves the exported function for every `UInt64` key.  The proof uses a concrete generated-constructor lemma for `func1`, expressed as a Boolean summary of Talos `run 5000` so it avoids equality over the whole `Store`; the summary exposes the root pointer, the list-cell memory layout, and the memory bound needed by loads.  The recursive search proof is symbolic over the key: each suffix theorem follows the generated `func0` body, splits on the stored key comparison, reads the hit value, or calls the theorem for the tail pointer.  The selected Wasmtime executions remain useful examples, but the Talos theorem no longer depends on enumerating those keys.

Checks run:

- [x] `lake build LeanExe.Examples.TalosAssocList lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.TalosAssocList --entry LeanExe.Examples.TalosAssocList.lookupDemo --out build/talos-assoc-list.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 7` returned `70`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 2` returned `20`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 9` returned `90`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 5` returned `0`.
- [x] `lake build Project.AssocList.Spec` proved the all-key Talos theorem for the decoded generated WAT.
- [x] `tools/check-talos-assoc-list.sh`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry leanPairListLookupDemo --result-slots '#[__leanexeValue]' --arg 7`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry leanPairListLookupDemo --result-slots '#[__leanexeValue]' --arg 2`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry leanPairListLookupDemo --result-slots '#[__leanexeValue]' --arg 5`

## 2026-06-19: WASI test compile cache

`test/wasi_program.js` now caches successful WASI compiles within one test-process run.  The cache key includes the compile mode, module name, entry name, and mode-specific limits, so input variants for one command reuse the same generated module while different modules that share an entry name such as `transform` get distinct output files.  Rejection tests still compile directly because those cases check diagnostics rather than a reusable executable artifact.

The output path now uses the same key fields instead of the entry name alone.  This removes accidental overwrites between modules such as `JsonGcd.transform`, `JsonTypedDecode.transform`, `JsonObjectArrayDecode.transform`, and `JsonGcTreeRewrite.transform`.  The final summary reports the number of successful compiles, which makes cache behavior visible without adding per-case output.

Checks run:

- [x] `node --check test/wasi_program.js`
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, 7 rejections, and 19 compiles` in `217.208` seconds.

## 2026-06-19: Plain Lean association-list proof

`LeanExe.Examples.TalosAssocList` now includes `lookupDemoExpected`, `LookupSpec`, and two observation relations.  The ordinary Lean theorem `lookupDemo_correct` proves `LookupSpec leanRunsTo`; the Talos theorem now proves the same shared `LookupSpec` instantiated with `wasmRunsTo`, where `wasmRunsTo` is the generated-WASM termination-and-stack observation.  The equality theorem `lookupDemo_eq_expected` remains as the source-level helper behind the plain Lean observation.

The Talos proof project now imports `LeanExe.Examples.TalosAssocList` through a local path dependency on the root `leanexe` package.  This keeps the expected-value function and the quantified spec in one Lean module, while leaving the WASM-specific observation relation inside the Talos proof file.

Checks run:

- [x] `lake build LeanExe.Examples.TalosAssocList`
- [x] `lake build Project.AssocList.Spec`

## 2026-06-19: Simple order-book example

`LeanExe.Examples.OrderBook` defines a small single-asset central limit order book example.  The book contains one best bid and one best ask, and `matchBook` accepts both the book and incoming order as `UInt64` inputs: bid quantity, bid price, ask quantity, ask price, side flag, order quantity, and order limit price.  Side flag `0` means buy, while every other flag means sell.

The match rule emits at most one `Option Trade`.  A buy crosses when its limit price is at least the best ask price, and the trade prints at the best ask price.  A sell crosses when its limit price is at most the best bid price, and the trade prints at the best bid price.  Trade quantity is the smaller of the incoming quantity and the relevant resting quantity, and this first example does not update the book.

The standard-comparison helper writes generated files under a path derived from module and entry.  It must run sequentially for multiple inputs to the same entry, or concurrent runs can overwrite each other.  The result observation for `Option Trade` uses three scalar projections: option tag, trade quantity, and trade price.

Checks run:

- [x] `lake build LeanExe.Examples.OrderBook lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.OrderBook --entry LeanExe.Examples.OrderBook.matchBook --out build/order-book.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 5 99 7 101 0 3 101` returned option tag `1`, quantity `3`, and price `101`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 12 200 4 250 0 9 250` returned option tag `1`, quantity `4`, and price `250`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 12 200 4 250 1 9 199` returned option tag `1`, quantity `9`, and price `200`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 12 200 4 250 1 9 201` returned option tag `0`, quantity `0`, and price `0`.

## 2026-06-19: Order-book Talos proof

The Talos proof project includes an `order_book` slice generated from the LeanExe WASM for `LeanExe.Examples.OrderBook.matchBook`.  `proofs/talos-gcd/lean/Project/OrderBook/Program.lean` is emitted from `proofs/talos-gcd/rust/build/order_book/program.wat`, and `Project.OrderBook.Spec` proves a quantified theorem about the exported `matchBook` function.  The theorem covers all seven scalar inputs: bid quantity, bid price, ask quantity, ask price, side flag, order quantity, and order limit price.

The theorem `matchBook_correct` states that the decoded WASM export terminates for every supplied one-level book and incoming order, returning exactly the expected option tag, trade quantity, and trade price.  Talos represents the WASM value stack with the top at the head of the list, so the proof names `tradeStackResult tag quantity price` as `[price, quantity, tag]`.  This is the reverse of Wasmtime's printed multi-result order, but it is the direct representation consumed by Talos's `TerminatesWith` predicate.

The proof follows the generated export `func1` and uses a separate lemma for the generated `minQty` helper `func0`.  It splits on the side flag and crossing predicate, proving the buy-crossing, buy-non-crossing, sell-crossing, and sell-non-crossing paths.  The proof artifact for this generalized scalar entry is `1207` bytes of WASM.

Checks run:

- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.OrderBook --entry LeanExe.Examples.OrderBook.matchBook --out proofs/talos-gcd/rust/build/order_book/program.wasm`
- [x] `$HOME/.cargo/bin/wasm-tools print proofs/talos-gcd/rust/build/order_book/program.wasm -o proofs/talos-gcd/rust/build/order_book/program.wat`
- [x] `proofs/talos-gcd/lean/.lake/packages/CodeLib/verifier/.lake/build/bin/verifier emit --force-emit order_book`
- [x] `lake build Project.OrderBook.Spec`
- [x] `tools/check-talos-order-book.sh`
- [x] `lake build Project`

## 2026-07-03: Talos documentation and check scripts

The top-level README now has a `Verification With Talos` section that explains the artifact proof path: LeanExe emits WASM, `wasm-tools print` renders WAT, Talos decodes the generated WAT into Lean, and the handwritten proof establishes a property of that decoded module.  The section links to the proof workspace, the Lean sources, the proof specs, and the per-case check scripts for GCD, association-list lookup, and order-book matching.  It also points users to `tools/check-talos.sh` as the combined artifact check.

`proofs/talos-gcd/README.md` now describes the proof workspace layout, the pinned Talos revision, the generated `Program.lean` files, the handwritten `Spec.lean` files, the checked-in WASM/WAT proof inputs, the current theorem scopes, the proof boundary, and the command path for regenerating `Program.lean` from an updated WAT artifact.  `spec.md` and `plan.md` now cross-reference the Talos artifact proofs while preserving the distinction between selected artifact proofs and the broader compiler-correctness theorem.  The GCD and association-list check scripts now use the same `wasm-tools print -o` form as the order-book script, and GCD now builds `Project.Gcd.Spec` instead of the whole proof project.  The combined `tools/check-talos.sh` script runs all three per-case checks and then builds the aggregate `Project` import.

Checks run:

- [x] `tools/check-talos.sh`
- [x] `git diff --check`
- [x] `bash -n tools/check-talos.sh tools/check-talos-gcd.sh tools/check-talos-assoc-list.sh tools/check-talos-order-book.sh`

## 2026-07-05: Repository summary and development agenda

`summary.md` describes the repository as it stands: the extraction pipeline, the accepted subset, the reference-counted arena memory model, the ABI and WASI adapters, the differential test suite, and the three Talos artifact proofs.  `agenda.md` sequences the next work: harden the Talos workflow, add the IR interpreter as a third differential semantics, measure heap leaks, then state and prove a lowering theorem for the scalar IR fragment, with the runtime `String` slice and backend module split behind those.  The agenda marks one design decision for discussion before the theorem work starts: whether the fragment theorem should speak about the WAT-decoded Talos module or a model built directly from the compiler's module value.

## 2026-07-06: Talos check script update mode

The three per-case check scripts are now thin wrappers over `tools/check-talos-case.sh`, which takes the case name, source module, entry, and proof spec target as flags.  The new `--update` flag replaces the checked-in proof inputs under `proofs/talos-gcd/rust/build` with fresh compiler output, regenerates the matching `Program.lean` through the Talos verifier emitter at `lean/.lake/packages/CodeLib/verifier/.lake/build/bin/verifier`, and rebuilds the proof.  Default mode keeps the byte-for-byte comparison.  `tools/check-talos.sh` forwards its arguments to all three cases.

Checks run:

- [x] `tools/check-talos-gcd.sh`
- [x] `tools/check-talos-gcd.sh --update` left a clean tree on an unchanged compiler
- [x] `tools/check-talos-assoc-list.sh`
- [x] `tools/check-talos-order-book.sh`

## 2026-07-06: IR interpreter differential column

The new `eval-ir` command compiles an entry to the core IR and evaluates it with the reference interpreter in `LeanExe/IR/Core.lean`, printing one unsigned decimal per result slot.  The interpreter is faithful only on the scalar fragment: heap constructs evaluate to `0` and `trap` evaluates to `0`.  `LeanExe/Extract/Eval.lean` therefore checks both the entry signature and the whole compiled module; any heap construct anywhere in the module exits with status `3`, and `tools/compare-standard.js` skips the IR column for that case.  The first self-test run caught exactly this: `idRunNestedArrayForSum` has a scalar signature but folds an internal array, and the signature-only check let the interpreter return `0` where WASM returned `10`.  The module scan replaced the signature-only check.

The interpreter `Store` is now a structure over `Array UInt64` with a `CoeFun` view, replacing the closure-chain function store.  The old representation added one closure per `set`, so loop evaluation was quadratic with large constants: `Collatz.steps 27` (fuel 10000) did not finish in fifteen minutes and now evaluates in under 0.2 seconds.  Extensional behavior is unchanged (`Store.empty` is all zeros, `set` shadows one index).

Pure-mode standard comparisons now run three semantics on the same inputs: standard Lean, the IR interpreter, and Wasmtime.  A mismatch localizes to extraction (standard versus IR) or emission (IR versus WASM).

Checks run:

- [x] `lean-wasm eval-ir --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps 27` returned `111`
- [x] `lean-wasm eval-ir` on `byteArrayReturnABC` and `idRunNestedArrayForSum` exited `3` with fragment diagnostics
- [x] `node tools/compare-standard.js --self-test` returned `checked 301 standard Lean comparison cases` and `checked 58 IR interpreter comparison cases`

## 2026-07-06: Host leak accounting

Library-mode modules now export the runtime counter globals `allocCount`, `retainCount`, `releaseCount`, and `freeCount` as mutable `i64` globals, extending the reserved export-name list.  The Wasmtime host runner has a `call-stats` command that invokes an export like `call` and then prints the four counters, and `test/wasmtime_host.js` exposes `callStats`.  `test/refcount.js` asserts exact counter quadruples for seven heap-using scalar-result entries and reports the leak balance.

Five entries run leak-free (allocations equal frees): `ownedArrayCallTempScalar`, `ownedByteArrayCallTempScalar`, `ownedBoxCallTempScalar`, `sharedRecursiveChildReleaseStats`, and `byteArrayResultDropsOwnedTempStats`.  Two retain blocks at exit.  `ownedRecursiveNodeParamCallTempScalar` allocates 3 and frees 0, which is the documented conservative policy for recursive temporaries.  `arrayFoldByteArrayAccumulatorReleaseStats` allocates 11 and frees 2, so nine blocks survive a fold that the accumulator-replacement rule was thought to cover; the unreleased blocks are candidates for the next release-rule extension and should be diagnosed before new rules are written.

The export change alters every generated library module, so the three Talos proof inputs were regenerated with `tools/check-talos.sh --update`.  The WASM and WAT inputs changed, each generated `Program.lean` came back byte-identical, and all three proofs rebuilt without repair: the Talos verifier emitter's model does not reflect the export section, so the weakest-precondition proofs are untouched by added exports.

Checks run:

- [x] `node test/refcount.js` returned `checked 7 leak accounting cases, 5 leak-free, 2 retaining blocks` and `checked 38 refcount cases`
- [x] `tools/check-talos.sh --update` regenerated all three proof inputs and rebuilt all proofs

## 2026-07-06: Fragment-theorem model question

The agenda's Priority 1 needs one design decision before the theorem statement can be written.  The theorem quantifies over IR programs in the scalar fragment and asserts that the emitted WASM module, read in the Talos model, computes what `Expr.eval` computes.  The question is how the Talos-model module value is obtained.

Option A keeps the current artifact path: the emitter produces bytes, `wasm-tools` prints WAT, and Talos's WAT decoder produces the module value.  The theorem then needs a connection lemma stating that decoding the printed form of the emitted bytes yields a module with the expected shape, which drags `wasm-tools` (a Rust binary) and the WAT decoder into the proof pipeline for every fragment program.  A universally quantified theorem cannot run an external binary, so Option A in its literal form only supports per-artifact proofs, which is what exists today.

Option B constructs the Talos-model module value directly from the compiler's own module representation in `LeanExe/Wasm/Binary.lean`, as a Lean function from the compiler's `Module` to Talos's module type.  The theorem then speaks about `talosModule (emit ir)` with no external tools, and the byte-level artifact comparison remains a separate check that the shipped bytes match the modeled module (per artifact, exactly as the check scripts do now).  The cost is a translation function and the obligation that it agrees with the WAT-decode path on the artifacts we ship; the existing byte-for-byte check scripts already discharge that agreement empirically per case.

Recommendation: Option B.  It is the only form in which a universally quantified fragment theorem can be stated, and it shortens the trusted path by removing `wasm-tools` and the WAT decoder from the proof loop.  The decision affects the `CodeLib` dependency surface (the translation function needs Talos's module type as a library) and should be confirmed before implementation.

Superseding note, same day: the user restated that the project's point is proving correctness of what is actually executed, which resolves the emphasis.  The deliverable is a proved artifact, so the per-artifact pipeline scales first and the general theorems enter later as cost reducers.  The Option A versus B framing partially dissolves under that reading; what matters is that each artifact theorem binds to the shipped bytes, which the check scripts already enforce.

## 2026-07-06: Transactional update mode

`tools/check-talos-case.sh --update` now backs up the checked-in WASM, WAT, and generated `Program.lean`, replaces them with fresh compiler output, regenerates the model, rebuilds the proof, and restores the backups on any failure.  Previously a failed update left unvalidated proof inputs in the tree that a later plain check would silently accept.  Each wrapper passes a new `--program` flag naming its generated model file.  The failed-update path was exercised repeatedly during the byte-validator proof development below and restored the tree correctly every time.

## 2026-07-06: Talos proof for byte validation over memory

The fourth Talos artifact proof covers `LeanExe.Examples.AsciiDigits.validateGeneric`, the repository's original first-milestone program: `ByteArray -> Bool`, scanning input bytes in linear memory through a fuel loop.  It is the first artifact theorem over the memory model with universally quantified input.  `Project.Validate.Spec.validateGeneric_correct` states: for every byte list, every store whose memory holds those bytes at a pointer (the `BytesAt` hypothesis, matching the `load8U` rule's address form and bounds side condition), and every pointer, the generated export terminates and returns `1` exactly when all bytes are ASCII digits.  The proof has no `sorry`, no added axioms, and no `native_decide`.

The proof decomposes along the generated functions.  `func0` (the digit test) and `func1` (the guarded byte load) get small `TerminatesWith` lemmas; `func1` discharges the load's bounds check and read value against `BytesAt`.  `func2` (the fuel loop) uses `wp_loop_cons` with a two-arm invariant: either the scan is at position `i` with every byte below `i` a digit and fuel exactly `length + 1 - i`, or the done flag is set and the result local holds the answer.  The measure is `2 * fuel + doneFlag`, which decreases through the flag-setting iteration where fuel is unchanged.  The export wrapper composes with `wp_call_tw`.  The shared `ValidateSpec` in the example file instantiates both the plain-Lean theorem (`validateGeneric_correct` over `validateFuel`, proved by induction on fuel) and the Talos theorem, mirroring the association-list pattern.

Two mechanical lessons for the next memory proof.  First, `wp_run` stops at every `iff`; the working cadence is `refine wp_iff_cons rfl ?_` to peel, then `rw [if_pos/if_neg (by simp [hyp])]` to choose the branch, then `wp_run` again, with the deciding hypotheses (`fuel ≠ 0`, index-versus-length, digit-versus-not, no-wrap) proved up front.  Second, the heartbeat budget is cumulative per theorem: the three-path loop proof needs `set_option maxHeartbeats 64000000` where GCD needed 8000000, and the final arithmetic goals need the `UInt64.size`-to-literal rewrite before `omega` because `omega` treats `UInt64.size` as an opaque atom.

Checks run:

- [x] `tools/check-talos-validate.sh --update` built the proof with zero errors
- [x] `tools/check-talos.sh` over all four cases plus the aggregate `Project` build

## 2026-07-06: Abstract heap predicate and shared proof lemmas

The association-list proof no longer hard-codes cell addresses.  A new inductive predicate `ListSegAt st addr kvs` describes a linked association-list segment in memory: each cell holds a tag word `1`, the key, the value, and the tail pointer in consecutive 8-byte slots, the terminator holds tag `0`, and every read carries its bound.  The generated lookup function gets one lemma, `func0_seg`, proved by induction over the list: for every segment and every key, the export returns the first matching value or `0`.  The four per-node lemmas at addresses 4464, 4384, 4304, and 4224, and their per-node expected-value functions, are deleted; the only place concrete addresses remain is `sample_seg`, which shows the constructed sample is a segment at its root.  The public theorem `lookupDemo_correct` is unchanged in statement, and the lookup lemma now applies to arbitrary constructed lists, which is what the next list-building artifact will need.

`Project/Common.lean` now holds the lemmas the artifact proofs share: `size_eq`, `toNat_ofNat_lt`, `ofNat_inj`, `toNat_add_one`, and `getBang_eq` from the byte-validation proof, plus the address-form conversions `toUInt32_toNat`, `toUInt32_ofNat_mod_toNat`, and `toUInt32_eq_ofNat` that connect `(addr + c).toUInt32` hypotheses to the modular normal form `simp` produces in wp goals.  The mechanical lesson: `omega` treats `addr.toUInt32.toNat` and `addr.toNat % 4294967296` as unrelated atoms, so segment-style predicates must be rewritten into the goal's normal form before the bounds discharge, and the conversions belong in one place.

Checks run:

- [x] `tools/check-talos-assoc-list.sh` built the refactored proof with zero errors
- [x] `tools/check-talos.sh` over all four cases plus the aggregate `Project` build

## 2026-07-06: Talos proof for byte append through the allocator

The fifth Talos artifact proof covers `LeanExe.Examples.ByteArrayPrograms.appendBang`, the first memory-writing artifact.  `Project.AppendBang.Spec.appendBang_correct` states: from any store whose free list is empty, whose heap-top global leaves room for the rounded allocation within current memory, and whose input bytes sit below the heap top, the export terminates, returns the fresh pointer `g0 + 48` and `length + 1`, the result region holds the input bytes followed by `33`, and every byte below the old heap top is unchanged.  The proof has no `sorry`, no added axioms, and no `native_decide`, and it verifies the inlined runtime allocator on its bump path: the free-list walk exits on its first test, the pointer-wrap and memory-grow guards discharge from the fit hypotheses, and the six reference-count header stores land above the old heap top.

The copy loop uses a two-clause memory invariant: the number of bytes already copied into the result region, plus a frame clause that everything below the old heap top equals the pre-call memory.  The frame clause is also part of the public theorem, so the statement rules out corruption of the caller's input.  Pointwise write reasoning goes through two small local lemmas, `write8` at the hit address and `write8` away from it, with the hit stated as an equation hypothesis so the rewrite never touches the address expression itself; the six `write64` header stores use the same shape with a generic address.

Mechanical lessons beyond the validate proof.  First, `wp_run` stops on locals bookkeeping when the frame comes from an invariant; a plain `simp` after `wp_run` collapses it, and branch conditions surface as `if a ≥ b` in `GE` form, so the deciding facts must be supplied as `≥`-typed terms for `if_pos`/`if_neg`.  Second, `simp only [Mem.write64]` across a six-write chain exceeds the step limit because of the literal byte-extraction arms; unfolding is avoided entirely by the generic one-write frame lemma applied six times with the disequality proofs inline.  Third, `simp` normalizes `(UInt64.ofNat k + 1).toNat` to `(k + 1) % 2^64` on its own, so measure goals close with `omega` directly.

Checks run:

- [x] `tools/check-talos-append-bang.sh --update` built the proof with zero errors
- [x] `tools/check-talos.sh` over all five cases plus the aggregate `Project` build

## 2026-07-06: Shared write-frame lemmas

`Project/Common.lean` now holds `write8_bytes_ne`, `write8_bytes_hit`, and `write64_bytes_lo`, and the byte-append proof uses them instead of local copies.  The hit lemma takes the address as an equation hypothesis so the rewrite never touches the address expression, which is the form the copy-loop and exit-store steps need.

## 2026-07-06: Fold leak diagnosis

The leak accounting flagged `arrayFoldByteArrayAccumulatorReleaseStats` at 11 allocations against 2 frees.  The diagnosis from the generated binary: the entry contains nine inline allocation sites, and at runtime the source-level costs decompose as one allocation for the `#[65, 66, 67]` literal, one for the starting accumulator, and three per fold iteration, of which only one is the copy-on-write `push` itself.  A direct push chain costs exactly one allocation per push (`bytesABC` runs at 3 allocations, 2 releases, 2 frees, with each replaced fresh predecessor reclaimed), so the fold body introduces roughly two extra allocations per iteration: intermediates from materializing the accumulator value into and out of the callback.  The accumulator-replacement rule fires correctly (2 releases, matching the source-level counters) but sees none of the intermediates, the initial accumulator is skipped by the documented alias rule even though it is provably fresh here, the input array literal is never released despite being a fresh nonrecursive owner in a scalar-result function, and the final accumulator leaks after its last use.  The release-rule work should target the per-iteration intermediates first, since they dominate and are provably fresh and dead within one iteration.

## 2026-07-06: compile-wat diverges from the emitted binary

Comparing `compile-wat` output against `wasm-tools print` of the `compile` binary for the same entry shows two different programs.  The binary contains the reference-counted runtime: paired free-list and bump allocation paths with header writes at every inline allocation site, and counter increments that match the observed runtime statistics.  The `compile-wat` output contains a headerless bump allocator with no free list and no counters: `moduleWat` in `LeanExe/Wasm/Binary.lean` is a second, hand-written WAT backend with its own hard-coded runtime, and it has drifted from the binary emitter.  The Talos proof pipeline is unaffected because the check scripts print WAT from the binary with `wasm-tools`.  Anyone reading `compile-wat` output, and any future proof work that trusted it, would be reasoning about code that does not ship.  The fix is a design decision: either derive the WAT text from the same lowering as `moduleBytes`, or retire `compile-wat` and document `wasm-tools print` as the inspection path.

## 2026-07-06: compile-wat removed

The decision: remove `compile-wat` now, and restore text output later on top of a structured backend that serializes the same lowering as `moduleBytes`.  The whole hand-written WAT backend is deleted from `LeanExe/Wasm/Binary.lean`, about 2,300 lines, along with the `compile-wat` command.  The two size-regression tests that compiled WAT now measure the compiled binary instead, which is the artifact whose size matters, with thresholds recalibrated against current output (`arrayStructureReplicateHelperRead` at 2,001 bytes against a 20,000 limit; the two JSON transforms near 49 KB against 200,000).  The README, manual, and specification point inspection at `wasm-tools print` of the compiled binary.  The structured-backend refactor, which also gives the fragment theorem its subject, is scheduled as its own piece of work.

## 2026-07-06: structured backend

The emitters in `LeanExe/Wasm/Binary.lean` now build `List Instr` values, where `Instr` is a small inductive in `LeanExe/Wasm/Instr.lean` covering exactly the instructions the compiler emits: constants, local and global access, calls, i64 arithmetic and comparisons, the handful of i32 operations, loads and stores at the three widths, memory size and grow, and structured control flow (`block`, `loop`, typed `if` with optional `else`, `br`, `brIf`).  A total function `encodeInstr` serializes each constructor to the exact byte form the fused emitter produced, and it is the only place instruction opcodes live.  Instruction-building atoms (`i64Const`, `localGet`, and the rest) shadow the byte-level helpers inside the `CoreWasm` namespace, so the emitter code above the encoder reads as before while producing structured values.  Byte-level code remains in three places: the leb128 and section-framing helpers, the function-body wrappers (`bodyI` encodes a body's instructions and prepends its local declarations), and the early WASI prototype at the top of the file.

The gate for the refactor was byte identity.  Fresh compiles of `appendBang`, `matchBook`, `steps`, and `arrayFoldByteArrayAccumulatorReleaseStats` are byte-identical to binaries snapshotted before the refactor, `tools/check-talos.sh` confirms all five proof artifacts unchanged and rebuilds every proof, and the full test suite passes (301 standard comparison cases, 58 IR interpreter cases, 56 runtime cases).  The encoder compiles without `partial`, so later work can prove facts about it by induction; the next step on this line is a `printInstr` WAT printer over the same `Instr` values, which restores `compile-wat` as a second serializer of the one lowering.

## 2026-07-06: release path proved over the free list

The sixth Talos artifact covers the allocator's release path.  The subject is a new example, `pushBangSize`, chosen because the optimizer eliminates slice temporaries: `(input.push 33).size` is the smallest program whose generated code materializes a heap object and then discards it, so the entry contains the full inline allocator followed by `call $release` on the fresh raw object.  The case is `tools/check-talos-push-size.sh`, registered in the aggregate script and the Talos crate workspace as `push_size`.

The proof splits at the call.  `func4_frees_fresh_raw` is a self-contained theorem about the release function: for any store holding a nonzero raw object with refcount one at `p` (stated as three `read64` header facts), running function 4 on `[p]` terminates with the refcount slot cleared, the old free-list head written into the next-pointer slot, global 1 pointing at `p`, and the release and free counters advanced; the postcondition gives the exact final memory as a two-write chain and the exact globals as a three-set chain.  The main theorem re-proves the appendBang allocation prefix with the copy-loop invariant extended by four header `read64` facts (magic, refcount, capacity, kind), which the write-frame lemmas carry across each byte copy, and then consumes the release theorem through `wp_call_tw`.  The final statement: the export returns `length + 1`, the free list ends at the released object with its capacity slot intact and next pointer zero, alloc, release, and free counters each advance by one, retains stay untouched, and every byte below the old heap top is unchanged.  No sorry, no axioms, no native_decide.

`Project/Common.lean` gains the word-granularity frame lemmas this needed: `write64_bytes_ne` (two-sided window disjointness), `read64_congr`, `read64_write64_ne`, `read64_write8_ne`, and `write8_pages`.  CodeLib's `Mem.read64_write64_same` supplies the read-after-write case.

## 2026-07-06: array literals allocate once

The fold-leak work started from the recorded diagnosis, and the new `dump-ir` command (a `reprStr` dump of the compiled IR module, added to the CLI next to `ownership-report`) immediately corrected it.  `arrayFoldByteArrayAccumulatorReleaseStats` had no per-iteration callback intermediates: its eleven allocations were two full constructions of the `#[65, 66, 67]` literal, four allocations each, plus one copy-on-write push per iteration.  The literal lowering built `arrayAllocSlots` followed by one copying `arraySetSlots` per element, and the fold's elaborated default stop bound `as.size` re-extracted the whole literal a second time.

Three compiler changes remove the waste at its source.  First, a new IR expression `arrayLiteralSlots width childMask elements` allocates once and stores each element's slots directly, with per-element owned masks deciding transfer against retain; `List.toArray` extraction now produces it instead of the set chain.  Second, fold extraction binds a non-local array expression to a fresh local, folds over the local, and reads the default stop bound from it, recognizing `Array.size` of the same source term; the letE-wrapped fold value converts to a preceding assign plus the existing fold-assign statement.  Third, ownership transfer inside a literal is consume-once: an owned local transfers at its first occurrence across the literal's slots and is retained at later ones, in both the extraction-time mask computation and the alloc-time mask refresh.  The first test run caught the need for this rule as a refcount underflow trap in `u64BinarySharedArrayScore`, whose literal stores the same child twice; the old set chain had masked the double transfer with its copy-time retains.

The measured entry drops from eleven allocations to four: one literal, three pushes, with releases and frees unchanged at two.  Three recorded expectations moved because the leaked set copies had held stale retains that kept children alive past their release: `optionByteArrayArrayRuntimeReleaseFrees` and `publicTokenArrayRuntimeReleaseFrees` gain one free (302 to 303), and `byteArrayGroupArrayRuntimeReleaseFrees` now tears its six-object tree down completely (403 to 606).  All 784 correctness cases, the comparison suites, and all six Talos artifact checks pass; the artifacts are byte-identical because none of the proved programs contains an array literal.  The remaining fold leaks are the input literal and the final accumulator, both single objects per fold.

## 2026-07-07: fold source and result released

The two remaining fold leaks close.  When fold extraction binds a constructed source array to a local, the fold-assign conversion now appends a release of that local after the loop, guarded by `exprBuildsFreshArray`, a conservative allowlist of array-constructing expressions that keeps the previous leak instead of risking a double release on anything it does not recognize.  The final accumulator closes through classification: `exprReturnsOwnedNonrecursiveHeapObjectFrom` now recognizes a fold value at an offset in its `releaseOffsets` as owned, provided the initial accumulator at that offset is itself owned or the null pointer, so the existing owned-temp release machinery frees the result after its last use.  The zero-iteration case motivates the init condition: a fold that never runs returns its initial accumulator, and releasing a borrowed init would corrupt.

The measured entry is now leak-free at four allocations, four frees, zero retains.  Six recorded expectations move by exactly the released input literal entering the measured window (30202 to 30303 and analogues), and the call-stats quad for the measured entry goes from 4/0/2/2 to 4/0/4/4.  All suites and all six Talos artifact checks pass with byte-identical artifacts.

## 2026-07-07: compile-wat restored as a second serializer

The `compile-wat` command returns on top of the structured backend.  `LeanExe/Wasm/Wat.lean` prints the module as WAT text: `instrLines` maps each `Instr` constructor to its text mnemonic, and the module skeleton (types, memory, globals, exports, function frames) mirrors the section builders in `Binary.lean`.  The function bodies come from the identical `List Instr` values the byte encoder serializes, factored out as `emitFuncInstrs` and `coreAllocInstrs`, `coreResetInstrs`, `coreRetainInstrs`, and `coreReleaseInstrs`; the byte bodies wrap the same lists, so the refactor is byte-preserving by construction and the artifact checks confirm it.

The gate is stronger than the old backend ever had: `tools/check-wat.sh` compiles nine entries (the six Talos programs, the measured fold entry, and a JSON transform), parses each `compile-wat` output back to a binary with `wasm-tools parse`, and requires byte identity with the `compile` output.  All nine match exactly, which pins not just semantics but section layout and LEB encoding.  The one fix the gate demanded was multi-result signatures: `matchBook`'s helper returns three values and the first draft printed at most one.  The README, manual, and specification present `compile-wat` as the inspection path again, with `wasm-tools print` as an independent view.

## 2026-07-07: free-list reuse case blocked on helper releases

The planned seventh Talos artifact needs a program that releases a raw object and then allocates again, so the allocator takes the free-list unlink path.  Three candidate shapes all fail to produce the release-then-allocate sequence.  A let-bound `(input.push 33).size` never releases the temporary: the owned-temp release machinery in `materializeResultValue` and `assignResultExprWithOwnedReleases` fires only on the top-level result value, and an intermediate scalar assign gets no releases.  The operand-nested form `(input.push 33).size + (input.push 34).size` fails the same way: the owned temporaries sit inside the operands of the result's `u64Bin`, and only top-level `letE`, `letLets`, and `letCall` shapes carry releases.  The composed form `pushBangSize input + pushBangSize input` compiles the helper without any release at all: `pushBangSize` as an entry contains `call $release` (the proved push_size artifact), but the same definition compiled as a helper in this module contains no calls, so the two temporaries leak and the second allocation extends the heap instead of reusing the freed node.

The entry-versus-helper difference is the item to fix first: both routes reach `materializeResultValue`, so the divergence is in how the helper's result value is shaped or flagged when it arrives there (`useAbi` differs between the paths).  Diagnosing that is the next step; the reuse artifact and its proof follow once a shape exists whose second allocation observes a nonempty free list.

## 2026-07-07: helpers release owned temporaries

The entry-versus-helper divergence is fixed.  In `materializeResultValue`'s fallback arm, the internal-ABI path converted a `LocalLet` holding a nested `letE` chain into one plain assignment, and the ownedness check saw only what the whole expression returns, so owned intermediates inside the chain never released.  The exported-ABI path flattens the same chain through `assignResultExprWithOwnedReleases`, which releases owned intermediate bindings.  The fallback arm now converts `.expr` and `.slots` lets through that same flattening (keeping the fold-assign conversion for fold-shaped slots), so helpers get the identical release discipline.  `pushTwiceSizes`, which calls `pushBangSize` twice, runs leak-free at two allocations, two releases, two frees, and its second allocation reuses the freed node from the first call's release.  The full suite passes with no expectation changes and all six Talos artifacts stay byte-identical, so no existing program shape was affected.

## 2026-07-07: free-list reuse proved

The seventh Talos artifact covers the allocator's unlink path.  `pushTwiceSizes` calls the compiled `pushBangSize` helper twice; with the helper-release fix in place, the first call's released temporary sits on the free list when the second call allocates, and the search loop takes the node instead of extending the heap.  The proof splits the helper's two behaviours into separate theorems over function 0.  `func0_empty` restates the push_size result for this module: bump allocation, with the released node's capacity and next pointer exposed for the caller.  `func0_reuse` is the new work: its free-list walk runs two iterations under a disjunctive invariant, the first taking the head node through the capacity test, the unlink store to global 1, and the header reinitialization, the second exiting on the result-local test; the copy loop then runs under a reuse variant of the invariant whose allocator state is the post-unlink state.  The release function's raw path is `func5_frees_fresh_raw`, the push_size theorem retargeted at this module's function table.

The entry theorem composes the two helper theorems through `wp_call_tw`, rebuilding the input `BytesAt` for the second call from the first call's below-heap frame, and discharges the result overflow guard.  The statement pins the reuse fact directly: the final heap top is `g0 + 48 + allocSize`, one rounded allocation above the initial top, while the alloc, release, and free counters each advance by two and the free list ends back at the reused node.  No sorry, no axioms, no native_decide.  All seven artifact checks pass.

## 2026-07-07: transfer accounting fixed for returned containers

The retain-artifact program exposed an ownership undercount.  `sharedPushPair` binds one push result and returns `#[appended, appended]`: the literal transfers the local at its first occurrence and retains it at the second, so the refcount must end at two.  The compiler emitted an additional guarded release of the local, leaving two live references backed by a count of one; the unshared `#[appended]` variant showed the same spurious release, dropping the sole reference to zero while the returned array still pointed at it.  The cause: the owned-temp release decisions in `materializeResultValue` consult the pre-materialization value view, whose literal owner masks are still empty, so the transfer of the local is invisible; the masks are refreshed with owner sources only during materialization.  The set-chain lowering had the same blind spot, untested because no existing case returned a container holding a let-bound owned local.

The fix reads the answer from what actually ships: a new `stmtReleasedSlots` scans the materialized body statement, which carries the refreshed masks, and the release decisions in the `letE` and `letLocal` arms now consult it alongside the value view; the flatten fallback also refreshes owner masks before its release accounting.  Both program variants now end with exact counts, and `free` on the returned array performs the full recursive teardown to refcount zero.  The full suite passes with no expectation changes and all seven Talos artifacts stay byte-identical.

## 2026-07-07: the inline retain sequence proved

The eighth Talos artifact is complete.  `sharedPushPair` builds `input ++ [33]` once and returns `#[appended, appended]`; the theorem proves that the returned array's cells alias the single temporary, its refcount ends at exactly two, the retain counter advances by one, the alloc counter by two, and everything below the old heap top is unchanged.  This is the first proof over the inline retain sequence the compiler emits for shared children: the magic check against a header the same proof wrote two allocations earlier, the refcount load, the counter increment, and the read-modify-write store from one to two.

Three mechanical lessons paid for the proof.  First, once the store carries the phase-two write chain, the standard `wp_run` simp set exceeds its step budget; a local `wp_run_big` macro with a ten-million-step limit replaces it, and a `set stB` binder folds the bang-written store to keep terms small.  Second, mixed address normal forms are the main hazard in a two-allocation proof: the `% 2^64` layer from heap-pointer sums needs one `Nat.mod_eq_of_lt` normalization before frame lemmas apply, offset subtractions must be reduced to literals eagerly (an unevaluated `UInt64.toNat 8` turns every omega atom opaque), and `(0 : UInt64).toNat` needs its `rfl` like every other literal.  Third, `simp only` with a hypothesis whose left-hand side is a thirteen-write chain fails to match where plain `rw` succeeds, so the big read-back facts rewrite with `rw`.  No sorry, no axioms, no native_decide; all eight artifact checks and the full test suite pass.

## 2026-07-07: recursive release proved through the array branch

The ninth Talos artifact closes the release function's coverage.  `sharedPairFreeStats` builds the shared pair through the compiled helper and releases it; the entry theorem pins the measured value at the literal 302, three releases and two frees, plus the free-list head and all four counters.  The recursion turned out not to need a measure-carrying `FuncSpec`: the object graph is depth two and the child states at the two recursive call sites are concrete, so `func7_frees_pair`, the array-branch theorem, consumes two leaf lemmas through `wp_call_tw` — `func7_decrements` for the first call, which lowers the shared child from two to one in a single store, and the raw-free lemma for the second, which puts the child on the free list.  The cell walk itself runs under nested loop invariants: a three-state outer disjunction indexed by the item, each step opening an inner four-state invariant over the slot, with the store equations evolving at the two call sites.  Composition order in the final state is exact: child at refcount zero, parent freed in front of it, free list reading parent then child.

The helper's construction theorem is the SharedPair proof ported to this module's local numbering, which a mechanical stream alignment of the two generated programs produced (one extra result temporary, everything else shifted), with the postcondition extended to the eleven header and cell facts the array branch reads.  New mechanical lessons: `simp` normalizes same-index `List.set` chains during invariant establishment, so invariants written as raw set-compositions bridge by `List.set_set`; counter cancellations over symbolic globals (`g4 + 1 + 1 + 1 - g4 = 3`) close by `bv_decide`; and a goal-side `rw` succeeds where `simp only` fails to index large chain hypotheses, as in the retain proof.  No sorry, no axioms, no native_decide.  All nine artifact checks and the full test suite pass.

## 2026-07-07: owned temporaries release in every statement position

The last two known temporary-leak shapes close.  Let-bound temporaries (`let first := (input.push 33).size` never released the push) now flatten through the release-aware assigner: the `letLocal` result arm and the internal-ABI fallback both convert their materialization lets with a shared `localLetStmtWithOwnedReleases`.  Operand-nested temporaries (`(input.push 33).size + (input.push 34).size`, where both pushes hide inside the operands of the result's addition) close through a new `exprSpineOwnedTemps` traversal: the plain-assign fallback of `assignResultExprWithOwnedReleases` collects owned `letE` binders along the expression spine — nested lets, both operands of scalar binary operations, and both branches of a conditional, which is safe because locals are zero-initialized and releasing null is a no-op — and appends guarded releases for those the expression neither consumes nor returns.  Both shapes now run at two allocations, two releases, two frees, with the second allocation reusing the first's freed node.  All nine proof artifacts stay byte-identical and the full suite passes unchanged.

## 2026-07-07: byteArray folds share and release their constructed source

The byteArray fold had the analog of the array-fold source duplication, worse by one: `wrapExprLets` wrapped the same construction lets around the pointer view, the length view, and the elaborated default stop bound, so a fold over a constructed byte array built its source three times and freed none of them.  The measured `foldFreshSum` ran at six allocations and zero frees.  Three changes close it: the fold value wraps the parts lets once around the whole fold expression instead of once per view; the elaborated default stop bound `b.size` on the same source term reuses the shared length; and the fold-assign conversion peels the value-let wrapper into hoisted assignments, converts the fold, and appends releases for wrapper binders that construct fresh objects.  The entry now runs at two allocations, two releases, two frees.  One recorded expectation moves for the same reason as before, the freed source entering the measured window (`byteArrayFoldByteArrayAccumulatorReleaseStats`, 30202 to 30404).  All nine artifacts stay byte-identical (parameter-sourced folds have empty wrapper lets and identical output) and the full suite passes.

## 2026-07-07: slots-release case blocked on flatten duplication

The tenth artifact was to cover the release function's slots branch through `chainFreeStats`, which builds a one-link recursive chain holding a pushed byte array and releases it.  The measured entry runs at five allocations against an ideal three: the constructor's slot values each embed a complete copy of the payload construction, so the push executes twice, and the extra copy leaks.  The cause is structural: `ByteArray.push` extraction correctly produces a value-level `letE` chain binding the construction once, but `flattenInternalValue`'s `letE`, `letCall`, and `letLocal` arms replicate the wrapper onto every flattened slot (`flattened.map (fun expr => .letE slot value expr)`), so any consumer that evaluates all slots — constructor materialization through `heapAllocSlots`, fold initial accumulators, and the rest — re-evaluates the binding once per slot.  The fold-specific fixes to date worked around exactly this at two call sites; the general repair is to route multi-slot consumers through the lets-materializing path (`materializeInternalValueLets`) instead of the expression-list flattening, which is an extraction refactor with a wide blast radius.  The slots-release proof waits on that fix: pinning an artifact over duplicated construction would certify code the repair is about to change.  The `chainFreeStats` example stays as the measured reproduction, at releases three and frees three against five allocations.

## 2026-07-08: slots-kind release proved

The tenth Talos artifact covers the release function's slots branch.  With correctness and simplicity ahead of the flatten repair, the subject sidesteps the duplication entirely: `boxFreeStats` builds a `UBox` chain (`node 1 7 nil`) whose slot values are scalars and a child pointer, so no construction wrapper exists to duplicate, and the shipped code is already the code worth certifying.  The entry theorem pins the measured value at the literal 202: two releases and two frees, with the free-list head at the node, both headers zeroed at the refcount word, and all four counters exact.

The release side is two lemmas over function 6.  `func6_frees_leaf` walks the three slots of the nil box under a four-state invariant, calls itself on the null slot through `func6_null` (the p = 0 early return), and frees the box.  `func6_frees_node` runs the same walk on the node, meets the live child pointer at slot two, and consumes the leaf lemma through `wp_call_tw` under a separation hypothesis keeping the child's header out of the parent's write frame.  The entry side hit an elaboration wall: the phase-two goal carries the phase-one nine-write chain in the store, and elaborating the whole entry in one theorem exceeded eleven gigabytes.  The repair is a cut: a private `boxPhase2` definition names the instruction suffix from the second allocation's free-list walk onward, and `boxPhase2_spec` proves it against a store described only by the read facts phase two needs — six header reads, six globals, and the page bound — so the write chain never enters the helper's elaboration.

Two composition lessons from the cut.  First, the helper's postcondition must be stated in the simp-normal form the entry goal reaches, not the library's `take ++ drop` form; even then the two match-expressions elaborate to distinct matcher constants that `refine` will not identify, and `wp.imp` — apply the helper, then discharge the postcondition implication by `cases c <;> exact h`, under which both matchers reduce — composes where direct application fails.  Second, the read facts bridge from the write chain by peeling `read64_write64_ne` frames outermost-in to the hit, with one `omega` rewrite collapsing the `% 2^64` layer on the slot addresses.  No sorry, no axioms, no native_decide.  All ten artifact checks and the full test suite pass.

## 2026-07-08: runtime lemmas proved once, consumed everywhere

The per-artifact cost survey confirmed the runtime suite is uniform: every generated module ends with the same four functions — allocate, reset, retain, release — byte-identical across all ten modules except for release, whose two recursive call sites embed its own function index.  That uniformity picks the mechanism for reusable lemmas without touching the compiler or any shipped binary: `Project/Runtime` now holds the shared instruction streams (`releaseBody` parametrized by its index), forty `rfl` checks pinning every module's runtime functions to them, and module-generic specifications taking the module and function index as parameters, with the lookup hypothesis each artifact discharges by `rfl`.

Four lemmas moved: `retain_spec`, `release_null`, `release_decrements`, and `release_frees_fresh_raw`.  The generic proofs are the concrete proofs nearly verbatim — the entry step passes the lookup and import hypotheses to `of_wp_entry_for` instead of computing them from the module constant, and no other step consults the module because the leaf paths never reach a call.  The five concrete copies across SharedPair, BoxFree, PairFree, PushSize, and PushTwice became one-line instantiations under their old names, so no call site changed: 517 lines of duplicated proof deleted for 24 lines of application.  A new program's proof now gets retain and the three release leaf behaviors for free; the recursive release branches remain per-shape, consuming these leaves through the call rule.  All ten artifacts prove unchanged.

## 2026-07-08: the frame-peeling boilerplate becomes a tactic

The read-over-write-chain derivation was the most repeated proof text: every header fact peels disjoint `read64_write64_ne` frames outermost-in with an omega side condition each, then lands on the syntactic hit.  `read_frames` in Common does exactly that as a `repeat first` loop, trying the hit lemma before each peel, so a stated read fact needs one word instead of a generated block; the sixteen peel blocks in the BoxFree spec, previously emitted by a script, are now single calls.  The stopping behavior is safe by construction: at the hit the separation omega fails and the loop halts, and an opaque base store matches neither lemma.  Alongside it, `toNat_sub_le` generalizes the subtraction bridge every proof re-derived as a local have; the general form needs the explicit `toNat_lt_size` bounds the local instances got from literal hypotheses in context.  All ten artifacts prove unchanged on top.

## 2026-07-08: fold_sum, the first artifact on the consolidated infrastructure

The eleventh Talos artifact validates the economics the runtime consolidation and the tactic layer were built for.  `foldSum` folds byte addition over its input; the theorem is input-generic in the strongest sense available: for every input byte list, the compiled export returns the value of the source-level fold and leaves the store untouched.  The loop invariant carries the fold over the consumed prefix, two ordinary list lemmas (`sumTake_succ`, `sumTake_le`) connect the prefix sum to the full fold and bound it below the wrap threshold, and the compiled overflow guard — the source addition is on `Nat`, so the compiler emits a trap on wrap — discharges against that bound.

The measured cost confirms the direction: the complete spec is 203 lines including the statement, the invariant, and both list lemmas, against 526 for push_size, the nearest comparable artifact, and it needed no per-proof lemma about the runtime because the entry never allocates.  The proof took four build iterations from skeleton to closed, each fixing one form mismatch.  All eleven artifact checks and the full suite pass.

## 2026-07-08: constructor fields evaluate once

The flatten duplication is fixed at its consumers.  `flattenInternalValue` replicates a field's value-level let wrappers onto every flattened slot, so a heap constructor whose field carried a construction chain re-evaluated the chain once per slot; a `ByteChain` node holding a pushed byte array executed the push three times, leaking two copies.  The repair peels each constructor field's wrapper chain before flattening (`stripExtractedValueWrappers`, threading the owner-source context each wrapper induces), flattens the residue, and re-wraps the chain once around the whole `heapAllocSlots` expression, at all three allocation sites: the internal flatten, the ABI flatten, and the array-element flatten.  A field without wrappers takes the byte-identical old path, so all eleven pinned artifacts are unchanged.

The reproduction confirms the fix statically and dynamically: the `chainFreeStats` module drops from 1818 to 1324 lines of text format — the two extra copies of the push construction gone — and the measured value stays exactly three releases and three frees, so the hoisted ownership masks are still exact.  Alloc-delta measurement inside the example turned out to be impossible: Lean's compiler folds two `allocCount` reads that bracket pure construction code into one, since the construction is pure at the Lean level; counter deltas only survive across opaque runtime calls, which is why the recorded expectations encode output size instead.  Deeper nesting — a field that is itself a product whose components carry wrappers — still replicates inside the residue and remains open.  The full suite and all artifact checks pass.

## 2026-07-08: release-tree model

`Project/Runtime/Tree.lean` models the object graphs the release function tears down, the base for a generic recursive-release theorem.  A `RelTree` is a slots-kind object at refcount one whose masked slots hold null, an owned subtree, or a shared object the walk only decrements; scalars fill the unmasked slots.  The first version keeps three restrictions: slots-kind only (arrays stay per-shape), all node addresses distinct (no aliased shared leaves inside one release), and shared objects as leaves.  `TreeAt` ties a tree to a memory through the header, mask, and slot-word reads the walk performs; `RelTree.events` lists the walk's writes in traversal order — children before their parent, so the free list ends at the root; `applyEvents` folds those writes over a memory and the free-list head, and `footprint` with `footprintOk` carries the per-node regions and their pairwise disjointness for the frame lemmas.  The staged plan: read stability under `applyEvents` outside the events' regions, `TreeAt` framing by mutual induction, then the release theorem by structural induction consuming the recursive calls through the call rule.

## 2026-07-08: the release-tree frame theorem

The frame infrastructure for the generic teardown theorem is proved.  `read64_applyEvents_ne` shows an eight-byte read separated from every event's header region passes through the whole event fold unchanged, and `applyEvents_pages` preserves the page count.  On top of them, `TreeAt_applyEvents` and `SlotsAt_applyEvents` show a tree's entire shape — headers, mask, slot words, and child subtrees — survives any event fold whose regions avoid the tree's footprint.  Two structural decisions came out of failed attempts: the shape predicates are mutual inductive predicates rather than recursive definitions, because destructuring a match-compiled recursive `Prop` tripped a kernel-level type mismatch in the elaborated term, and the mutual induction runs on an explicit size fuel rather than Lean's mutual well-founded recursion, which hit the same kernel error through tactic-mode `cases` on the decreasing argument.  What remains for the theorem is the walk itself: the loop invariant over the slot index with the prefix of events applied, the recursive call consuming the induction hypothesis through the call rule, and the composition of the event folds.

## 2026-07-08: event containment and composition lemmas

The remaining supports for the teardown theorem's walk: `applyEvents_append` composes event folds over concatenation; `regionSub` with `regionsDisjoint_of_sub` transfers disjointness through containment; `events_sub` (fuel induction again) places every event's header region inside a footprint region of its own subtree, and `events_bounds` derives the pointer bounds from the footprint bounds.  Together with the frame theorem these give the walk proof everything it consumes: sibling disjointness pushes each child's events away from every other region, so headers stay readable and untouched subtrees stay intact as the loop advances.

## 2026-07-08: mask bits characterized

`natMask` computes the mask word the compiler stores for a slot list, and `natMask_testBit` identifies bit `k` with whether slot `k` is masked — the fact the walk's shift-and-test branch condition reduces to.  `natMask_lt` bounds the mask below `2 ^ length` for the shift arithmetic.  With these, every support the generic walk proof consumes exists; the walk theorem itself — the wp induction over the tree with the slot-loop invariant carrying the prefix of applied events — is the remaining piece.

## 2026-07-08: walk preamble proved

`TreeSpec.lean` holds the per-iteration facts for the generic walk: `slotsMask_shift_and` reduces the compiled shift-and-test branch condition on the stored mask word to the slot's kind, through the `Nat.testBit` characterization and the 64-bit shift semantics; `SlotsAt_get` indexes a slot predicate to the k-th read fact and child shape; `sizeOf_child_lt` feeds the fuel induction.  The walk theorem itself is what remains: the wp induction over the tree, with the loop invariant carrying the prefix of applied events and the recursive call consuming the induction hypothesis through the call rule.

## 2026-07-08: the generic teardown theorem proved

`release_frees_tree` closes the largest open item in the runtime lemma library: for any module carrying the shared release function, releasing the root of an ownership tree frees every owned node in traversal order, decrements every shared leaf, and leaves the free list at the root, with the release and free counters exact and every other global untouched.  The statement quantifies over the tree, so a new program's recursive teardown proof reduces to exhibiting `TreeAt`, footprint disjointness, and the page bound — no per-shape walk proofs.

The proof is a fuel induction whose node case runs the release prologue generically, then the slot loop under an invariant carrying the prefix of applied events: at slot `k` the memory is the event fold of the first `k` slots' teardowns, the counters have advanced by the prefix sums, and the free-list head is the fold's second component.  Each masked slot dispatches on its kind — a scalar skips, a null consumes the generic null lemma, a shared leaf would consume the decrement lemma through the same path, and an owned child consumes the induction hypothesis through the call rule, with the frame theorem lifting the child's shape over the earlier siblings' events and the footprint decomposition supplying the disjointness.  The exit branch skips the array arm and composes the parent's own free event onto the prefix through `applyEvents_append`.  Mechanical lessons: simp reshapes an invariant proposition between the loop lemma and the re-establishment goal, so the tuple must match the reshaped form; equation-style `rfl` lemmas beat simp on fold unfoldings; and counter arithmetic over `UInt64.ofNat` closes by injectivity into `Nat` with omega once the literal `toNat`s are evaluated.  No sorry, no axioms; the whole proof library builds.

## 2026-07-08: documentation overhaul

The verification documentation caught up with the work.  The proofs workspace README now describes the current architecture — the pinned runtime suite, the module-generic lemma library, the tactic layer, the release-tree model with the teardown theorem, and the two statement templates — with a complete eleven-artifact table replacing the five-artifact one.  A new top-level guide, `verifying.md`, records the end-to-end recipe for verifying a program, from source through scaffolding, runtime pins, statement, proof, and gates, with `fold_sum` as the worked example.  `agenda.md` was rewritten around the actually open work: a demand-driving target program, retiring the per-shape teardown proofs by lifting the tree theorem's restrictions, the fragment-level lowering theorem, the remaining compiler simplifications, and proof-layer ergonomics.  `summary.md`'s module inventory reflects the backend split and current line counts, its verification section describes the library organization, and its observations section drops the items this session closed.  The root README's Talos section defers to the workspace table instead of duplicating a stale copy.

## 2026-07-08: the compiler's LEB128 core compiles itself

First milestone on the `self-emit` branch.  `LeanExe/Wasm/Leb.lean` holds the LEB128 encoders inside the accepted subset: mutable `ByteArray` loops in `Id.run`, ten bounded iterations, and an arithmetic shift built from bit operations, since the subset has no `Int`.  The native encoder in `Binary.lean` now calls these definitions through thin wrappers — an `intBits` bridge converts its signed `Int` interface to the two's-complement bit pattern — so the shipped compiler and the self-compiled artifact run the same code.  The swap is byte-exact: all eleven Talos artifacts compare identical and the full suite passes untouched.

`test/self_emit.js` states the fixed point: the compiler compiles its own encoder to WASM, and the artifact's output equals an independent JavaScript reference over thirty-nine boundary values covering the full unsigned range, the seven-bit group edges, and the signed termination conditions on both sides of zero.  The next slices move outward through the encoder: the vector and section combinators, then instruction encoding, with a Talos proof of the LEB artifact as the verification target.

## 2026-07-08: the compiler's encoder self-compiles; its proof is partway

The `self-emit` branch reaches the milestone it set out for: the compiler's own WASM byte encoder, compiled by the compiler, produces the same bytes as the compiler emits natively.  `LeanExe/Wasm/Leb.lean` holds the LEB128 encoders and the vector and section combinators inside the accepted subset, written as fuel recursion over mutable `ByteArray` loops; the native encoder in `Binary.lean` calls these same definitions, so the shipped compiler and the self-compiled artifact run identical code.  Both swaps are byte-exact: all eleven prior Talos artifacts compare identical and the full suite passes.  `test/self_emit.js` states the fixed point — the self-compiled `u32lebU64` and `s64lebU64` artifacts match an independent reference over sixty-three boundary values spanning the seven-bit group edges and the signed termination conditions, and the vector and section combinators likewise.  This is the self-hosting result: a nontrivial part of the compiler's back end verified by running as one of its own outputs.

The Talos proof of that artifact is partway.  `LeanExe/Wasm/LebTheorems.lean` proves `u32lebU64_eq_lebList`, identifying the shipped encoder with a pure recursion by fuel induction.  In the proof workspace, `Project/LebU32` carries the artifact model, the runtime pins, and the sorry-free step lemmas: `copyStepPos` (one byte-copy iteration), `tailStepPos` (the final-byte store re-establishing the loop invariant in the done state), and the pos-branch iteration scaffold in `Iter.lean`.  The 8-byte-uniform-capacity bump allocation, the empty-free-list walk, the six header stores, and the copy loop are all discharged.  What remains is the continuation-byte branch — the mirror of the final-byte path, re-establishing the invariant with the running flag and `v / 128` — and the export wrapper over `func1`, then `func0_encodes` composes them into the statement that the export returns a pointer to exactly `lebList 10 n`.  The byte-identity check gates the self-compiled artifact; the full correctness theorem is deferred, not abandoned.

## 2026-07-09: the self-compiled LEB128 encoder is proved correct

The twelfth Talos artifact closes the self-hosting loop.  `u32lebU64_correct` states that the compiler's own unsigned LEB128 encoder, compiled by the compiler, returns for every `n` below `2 ^ 32` a pointer to a buffer holding exactly the bytes of `lebList 10 n`, together with its length, leaving every byte below the old heap top unchanged.  `LeanExe/Wasm/LebTheorems.lean` proves the shipped source encoder equal to that same `lebList`, so the two compose: the WASM the compiler emits for its own encoder computes the encoder.  No sorry; the axiom set is `propext`, `Classical.choice`, `Quot.sound`.

The proof is four sorry-free lemmas over the generated model.  `copyStepPos` and `copyStepNeg` discharge one iteration of the buffer copy.  `posIterLemma` and `negIterLemma` each prove one iteration of the compiled fuel loop -- the eight-byte-uniform bump allocation, the empty-free-list walk, the six header stores, the copy loop, and the byte store -- differing only in the emitted byte and in whether the loop invariant is re-established in the done state or the running state (fuel decremented, `v` replaced by `v / 128`).  `func0_encodes` runs the outer loop under `lInv`, dispatching on the rest test to one lemma or the other, and `u32lebU64_correct` composes the export wrapper through the call rule.

The proof found nothing wrong with the compiler or the emitted artifact.  It cost two mistakes of my own, recorded here because both are easy to repeat.  First, I defined `posProg` and `negProg` as the selector's then- and else-blocks with a trailing `.br 0`.  `wp_iff_cons` runs the chosen block alone under a continuation that handles the remaining instructions, so the branch programs must exclude the `.br 0`, and each iteration lemma's final obligation is a `Fallthrough`, not a `Break 0`.  The lemmas proved under the wrong definitions were true statements about the wrong programs, so they simply would not apply.  Second, I claimed Lean was behaving nondeterministically.  It was not: six builds from a fully-clean olean set are byte-identical.  The divergence came from rebuilding one olean while leaving a stale sibling whose lemma statement had since changed.  The real obstacle underneath is ordinary and documented: `exact` and `change` check definitional equality at bounded transparency and will not unfold a `def` down through `wp` and `exec`, so a lemma stated over a program name cannot be matched against a `wp_run`-reduced goal.  State the lemma so no such bridge is needed.

One performance lesson: proving `(g0.toNat + 56 * j + 48 + j) % 4294967296 = g0.toNat + 56 * j + 48 + j` with `by omega` inside a `rw [show ...]` dominated `posIterLemma`'s elaboration.  Hoisting the bound as a hypothesis and rewriting with `Nat.mod_eq_of_lt` took the file from exceeding four million heartbeats to seventy-eight seconds.

## 2026-07-09: a CLOB kernel from scratch, compiled and scaffolded for proof

`LeanExe/Examples/Clob.lean` is a central-limit-order-book kernel written from scratch in the accepted subset, shaped for proofs: fuel recursion for the maker search and the matching loop instead of `Id.run` for-loops, a flat `Array Order` book in time order, and scalar `UInt64` fields throughout.  Operations: `postOnly`, `limit`, `market`, `cancel`, `quote`, and `depth`, plus a scalar `scenario` entry that runs a fixed operation sequence and folds every result into a checksum.  Matching preserves FIFO among equal prices by keeping the first index on ties, skips same-trader makers, and treats market orders as price-unlimited.  The leanclob kernel served as a design reference; no code was ported.

`LeanExe/Examples/ClobTest.lean` holds the source-level guards: branch behavior for all four statuses, partial and full fills, FIFO on price ties, same-trader skipping, quote aggregation at the best price, and depth aggregation per side.  `report` classifies every entry as implemented by the first generic compiler fragment, and all seven entries compile.  Differential checks pass: `compare-standard --mode pure` matches on six `scenario` seeds, and `--mode pure-abi` matches `cancel` through the public array-of-structures ABI.  Two harness details worth remembering: with `--abi-arg` present the harness ignores `--arg`, so scalars also travel as `--abi-arg`, and structure values in `--abi-arg` and the serializer are JSON objects keyed by field name.

The thirteenth Talos case is scaffolded as `clob_quote`: `quote` reads the book and returns six scalars, so it exercises the array-of-structures input without heap results.  The artifact is pinned, the model is generated, and the runtime pins hold by `rfl` (`func11` through `func14`, release at index 14).  The export takes one `i64` (the book pointer) and returns six `i64` values.  The proof needs one new piece of machinery: a segment predicate for an array of five-slot structures in memory, the `ListSegAt` pattern from `assoc_list` lifted to fixed-width elements, with the loop invariant carrying the source fold over the consumed prefix.  Statement and proof are the next work.

- [x] Kernel builds; guards pass.
- [x] All entries compile; `scenario` and `cancel` match standard Lean.
- [x] `clob_quote` case scaffolded, pinned, model generated, runtime pinned.
- [x] `ClobQuote` spec stated and proved.
- [ ] Artifact theorems for `cancel`, `postOnly`, then `limit`.

## 2026-07-09: the thirteenth artifact: `quote` over every book in memory

`Project.ClobQuote.Spec.quote_correct` is proved, sorry-free, on the standard
axiom set (`propext`, `Classical.choice`, `Quot.sound`).  The statement: for
every order list laid out in memory as a length word followed by five words
per element, the compiled `quote` export returns the six fields of the source
fold and leaves the store untouched.  This is the first input-generic theorem
over an array-of-structures input.  `tools/check-talos.sh` passes for all
thirteen cases, and the differential suite passes untouched.

The proof splits into three modules.  `Step.lean` proves `func9`, the
compiled `quoteStep`: a pure 770-instruction branch tree that recomputes the
branch conditions once per output field.  The proof case-splits on the eight
source-level leaves and walks each with a `wp_step` macro that peels one
`iff`, decides every `ite` in its condition by `split` with contradictory
branches killed by `exfalso; simp_all`, and advances.  `norm_num` closes each
leaf.  `Spec.lean` holds the export theorem: the `OrdersAt` predicate states
every read in the exact normal form the walk produces
(`UInt32.ofNat ((ptr.toNat + (j * 5 + c) * 8) % 4294967296)`), so the loads
rewrite without address bridging.  The loop uses the `fold_sum` invariant
pattern with thirty-six existential scratch slots, and `func9_spec` transfers
the accumulator step through `wp_call_tw`.

Three lessons cost most of the day.  First, `TerminatesWith` value lists are
top-of-stack first: arguments arrive reversed relative to WASM parameter
order, results run from the last push down, and the frame stores parameters
in WASM order.  Second, a failing term-level `by` inside
`rw [if_pos (by ...)]` elaborates to `sorry`, logs an error, and lets the
rewrite take the wrong branch anyway; deciding branches at the tactic level
with `split` avoids the silent wrong turn.  Third, `wp_run` over the export's
59-local frame ground without converging on the 55-instruction loop-body
epilogue, because every step re-traverses the loop-exit continuation carried
in the postcondition.  `Epilogue.lean` cuts that tail into five segment
lemmas, each generic in the continuation and binding only the frame slots it
mentions; each walks in about two seconds where the monolithic walk did not
finish in twenty minutes.  The binder minimization is load-bearing: a segment
lemma that binds slots its frames never mention cannot be applied, because
unification has nothing to synthesize them from.

- [x] `func9_spec`: eight leaves, 179 seconds.
- [x] `epilogueA`-`epilogueE` segment lemmas.
- [x] `quote_correct`, sorry-free, standard axioms.
- [x] `tools/check-talos.sh` green for all thirteen cases.
- [x] `node test/run_all.js` green.

## 2026-07-09: the fourteenth case: `cancel` not-found, plus the scan lemma

`Project.ClobCancel.Spec.cancel_notFound` is proved, sorry-free, on the
standard axiom set: for every order array in memory and every id absent from
it, the compiled `cancel` export returns status three and the borrowed input
pointer, and the store is untouched.  The full Talos suite and the
differential suite pass.

The reusable piece is `scanFlag_spec` in `Project/ClobCancel/Scan.lean`: the
compiled id-scan loop, stated over the literal block-loop program with a
generic continuation, concluding at either exit with `List.findIdx?` as the
list-level bridge (`idIdx`).  The compiled `cancel` runs that identical scan
three times — once for the status flag, once to select the branch, once to
recompute the index — so one lemma discharges two call sites now and the
third when the found branch is proved.  The triple scan is itself a gap-list
entry: the extractor re-evaluates `findIdx?` once per use of the match
result rather than binding it once, tripling both code size and proof
obligations for this shape.

Two mechanical notes.  With a generic continuation the load trap-guards stay
as `ite`s rather than collapsing to conjunctions, and close with
`if_neg (Nat.not_lt.mpr hbound)`.  And full `simp` inside the loop-body walk
normalizes `getElem!` to `getElem?.getD` and discharges trivial invariant
conjuncts, so re-establishment tuples start at the existential and
hypothesis transfers go through `simpa`.

The found branch remains: it needs the index-recording scan variant and the
erase path, whose inline bump allocation, header stores, and two
element-copy loops follow the `append_bang` and LEB templates.

- [x] `scanFlag_spec` over the literal scan program.
- [x] `cancel_notFound`, sorry-free, standard axioms.
- [x] All fourteen check scripts and the differential suite pass.
- [ ] `cancel` found branch: index scan variant, inline allocation, copy loops.
- [ ] `postOnly`, then `limit`.

## 2026-07-13: Repository review and replacement development plan

The repository review covered the tracked source, extraction pipeline, IR interpreter, structured WASM backend, CLI, execution tests, ownership diagnostics, documentation, recent history, and the Talos proof workspace.  The untracked `leanclob/` directory is a separate nested Git repository, so the review excluded it except as background already recorded in the journal.  The old [Development Plan](plan.md) described an early compiler roadmap whose principal language, memory, WASI, comparison, and artifact-proof milestones now exist.

The replacement plan starts with two concrete compiler issues.  Source-level `LeanExe.Runtime.release` still relies on an unchecked ownership precondition, and CLOB `cancel` repeats one `findIdx?` scan three times while flattening its result.  The work order checks explicit-release ownership, evaluates matched values once, regenerates and proves complete `cancel`, then proves `postOnly`, `limit`, and `market` while extracting shared proof lemmas only from repeated cases.

The review also found documentation and tool gaps.  [Repository Overview](README.md), [Talos Proofs](proofs/talos-gcd/README.md), [Technical Summary](summary.md), and [Development Agenda](agenda.md) describe eleven artifacts, while the aggregate script now checks fourteen; CLI help omits `dump-ir` and `compile-wat` and retains a prototype-era scope sentence.  The root workspace pins Lean 4.29.1, the proof workspace pins Lean 4.31.0 and Talos commit `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`, and Wasmtime defaults to 44.0.0, while `wasm-tools` and Node have no recorded versions and the Wasmtime download script does not verify archive checksums.  The plan schedules version checks and archive verification after the active semantic work.

The ordinary execution gate passed.  `node test/run_all.js` reported 114 classification cases, 8 ownership-report cases, 784 accepted cases, 34 rejections, 13 traps, 38 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, 4 integer-map cases, 48 JSON cases, 35 WASI cases with 2 traps, 7 rejections, and 19 compile-only checks, 63 self-emitted LEB128 cases, 301 standard-Lean comparison cases, 58 IR-interpreter comparison cases, and 56 fuzz cases.  One leak-accounting fixture intentionally retains blocks, while the other six reported leak-free behavior.

The artifact gate also passed.  `tools/check-talos.sh` compared all fourteen regenerated WASM and WAT artifacts with their checked-in proof inputs and rebuilt the aggregate `Project` library.  The cold proof workspace first built 3,003 dependency jobs, and the final aggregate build completed 3,048 jobs; Lean reported unused `simp` arguments and variables in handwritten source and proof files, but no artifact mismatch, proof error, `sorry`, or new axiom.

Review references are [Language Specification](spec.md), [User Manual](manual.md), [Verifying a Program](verifying.md), [Talos Proofs](proofs/talos-gcd/README.md), [Core IR](LeanExe/IR/Core.lean), [Structured WASM Instructions](LeanExe/Wasm/Instr.lean), [Compiler CLI](LeanExe/CLI.lean), and [CLOB Source](LeanExe/Examples/Clob.lean).  These repository files define the current implementation and claimed behavior.  The replacement plan keeps their roles separate and schedules a factual consistency pass.

- [x] Review the tracked repository and recent development history.
- [x] Run the complete execution suite.
- [x] Run all fourteen byte-pinned artifact checks and the aggregate proof build.
- [x] Replace the obsolete development roadmap with current priorities and exit conditions.
- [x] Check the ownership precondition for source-level release.
- [ ] Bind repeated match results once and reduce CLOB `cancel` to one identifier scan.
- [ ] Prove complete CLOB `cancel`, followed by `postOnly`, `limit`, and `market`.

## 2026-07-13: Developer guide and documentation consolidation

[Developing LeanExe](DEVELOPING.md) now defines the developer entry path.  It records the Lean 4.29.1 compiler workspace, the Lean 4.31.0 proof workspace, Wasmtime 44.0.0, the unpinned Node and `wasm-tools` gaps, system prerequisites, environment overrides, first-build commands, diagnostic commands, test gates, tracked proof artifacts, update transactions, dependency rules, and failure diagnostics.  The guide also assigns one responsibility to each maintained document so current facts do not require parallel edits in several roadmaps.

The current-state documents now agree with the aggregate proof script.  The repository overview and technical summary report fourteen artifacts, and the Talos README lists the unsigned LEB128, CLOB quote, and CLOB cancel theorems with the exact limitation that cancel covers only an absent identifier.  The technical summary no longer records volatile file sizes or test totals, `agenda.md` is an archived pointer to the development plan, the two early Talos documents identify themselves as historical experiments, and the string document identifies itself as an unimplemented proposal.

The implemented diagnostic commands now appear in every relevant interface.  CLI usage includes `dump-ir` and `compile-wat` and replaces the prototype-era scope sentence, while the repository overview, manual, specification, technical summary, and verification guide explain their roles and the proof-workspace setup.  The manual sends tool and build failures to the developer guide instead of mixing them with source rejection advice.

Documentation verification passed.  A local-link check covered all sixteen repository Markdown files, the Talos table and aggregate script each contain fourteen cases, the stale-current-state scan found no remaining eleven-artifact or prototype claims in maintained documents, and `git diff --check` reported no whitespace errors.  `lake build lean-wasm` completed 46 jobs, the no-argument CLI displayed the corrected command list with exit status 2, `dump-ir` succeeded for `LeanExe.Examples.TalosGcd.gcd`, and `node test/report_classification.js` passed all 114 cases.  The build still reports the existing unused `hsize` `simp` argument in `LeanExe/Examples/AsciiDigits.lean`; the plan keeps that warning cleanup separate from documentation work.

The execution and artifact gates recorded in the preceding review remain applicable because these edits changed documentation and CLI usage text without changing extraction, IR, ownership, ABI, or WASM emission.  The targeted CLI build and report-classification test cover the executable change.  No proof input or generated model changed.

## 2026-07-13: Development plan semantic review

A second review of `plan.md` found that its first release-ownership phase combined two different problems.  `LeanExe.Runtime.release` and the runtime counters have compiled behavior that differs from their ordinary Lean stubs, so an ownership check alone could not support the plan's source-equivalence language.  The phase also asked one change to recognize aliases through locals, structures, tags, arrays, helpers, and returns, even though the current ownership summaries support a narrower direct-handoff judgment.

The revised phase now defines the runtime-intrinsic semantic boundary before implementation and treats release as consumption of one owned root reference rather than graph-wide uniqueness.  Its first accepted subset is a direct fresh local or fresh helper result at final use, plus a statically known owner-zero array release; branch-dependent ownership, container escapes, loop-carried fields, and unresolved aliases reject until a later focused increment proves them.  The plan removes the proposed test-only bypass, requires an inventory of every existing explicit release, and separates ordinary Lean comparison claims from claims under LeanExe's runtime extension.

The matched-value phase now requires reduced tests for unused trapping payloads and heap-bearing results in addition to the CLOB scan count.  The CLOB proof phase defines `UInt64` source equivalence separately from natural-number conservation with no-overflow bounds, states shared layout and ownership preconditions, proves `findBest` before `postOnly`, and proves `matchFuel` before `limit` and `market`.  `depth` now appears in both the proof scope and the completion criteria.

The baseline now records the completed documentation work and the remaining tool gaps.  CLI errors, Node and `wasm-tools` versions, Wasmtime hashes, cold-build reporting, and known warnings form a numbered phase required by the next stable point.  The general lowering theorem moved to later work because the completion criteria do not require it, and the proof-consolidation phase now runs during CLOB proofs once repetition establishes a common statement.

The documentation baseline was committed as `5659ef5` before this plan revision.  The plan link resolves, its prose passes the repository style scan, and `git diff --check` reports no whitespace errors.  No compiler, artifact, proof, or generated model changed in this revision.

## 2026-07-13: Runtime intrinsic semantics and release audit

The runtime intrinsic boundary now has one explicit semantic statement.  Ordinary Lean and the reference IR interpreter evaluate the four counters and `LeanExe.Runtime.release` as zero-valued stubs, while generated WASM maintains allocator counters and consumes one owned root reference.  A nonzero release validates the root, increments the release counter, decrements its reference count, recursively decrements marked children when the count reaches zero, increments the free counter, and returns the resulting free count; owner `0` changes no state.

The source judgment concerns the released root reference rather than graph-wide uniqueness.  Release requires final use of a direct fresh local or fresh helper result, without a copied alias, return, container escape, or repeated release; a statically owner-zero array also qualifies as a no-op.  A child shared through a retained reference may remain live, while branch-selected roots, conditionally owned arrays, structure fields, loop-carried roots, consuming parameters, and unresolved aliases require analysis beyond the initial judgment.

The tracked example source contains twenty-two explicit release calls.  Eleven consume direct fresh roots, four consume fresh helper results, one consumes a branch-selected fresh root, two consume conditionally owned array-operation results, one releases a statically owner-zero out-of-bounds update, one consumes a function parameter, and two consume roots carried in structures.  The table records the source classification that the compiler checker and focused tests must reproduce.

| Source release sites | Count | Audit result |
|----------------------|-------|--------------|
| `Correctness`: inline replicate, three nested or structured arrays, `unusedRecursiveRuntimeReleaseFrees`, `sharedRecursiveChildReleaseStats`, and three public-layout arrays; `ByteArrayPrograms`: `boxFreeStats` and `chainFreeStats` | 11 | Direct fresh root with no root use after release.  The shared-child case remains valid because construction retains the second child reference. |
| `Correctness.recursiveScenarioHelperRuntimeReleaseStats`, `ByteArrayPrograms.sharedPairFreeStats`, and both roots in `JsonMergeTreeCommand.makeMergedTreeValue` | 4 | Helper result whose fresh root must appear in the helper ownership summary. |
| `Correctness.recursiveScenarioRuntimeReleaseStats` | 1 | Fresh on every branch, but provenance is branch-dependent and lies outside the initial checker. |
| `Correctness.borrowedArrayPopEmptyReleaseFrees` and `borrowedArrayReverseSingletonReleaseFrees` | 2 | The result may borrow or own according to the input and operation path, so the initial checker must reject it. |
| `Correctness.borrowedArraySetOobReleaseFrees` | 1 | The index equals the source size, making the update a statically borrowed owner-zero no-op. |
| `JsonTreeCommand.insertOwned` | 1 | Consumes a function parameter after building a replacement and requires a consuming-parameter judgment. |
| `JsonGcTreeRewrite.runRoundsFuel` and `runConfig` | 2 | Consume a loop-carried structure field and a helper-result field, which require field-sensitive ownership analysis. |

The specification, manual, repository overview, and developer guide now state the same boundary.  The first compiler increment will accept only the direct cases and owner-zero case, reject unsupported provenance with the declaration and released expression, and expose the judgment in the ownership report.  Existing command examples that rely on consuming parameters or structure fields need a later proved increment or a source revision that exposes a direct handoff.

- [x] Define generated runtime counter and release transitions.
- [x] Separate ordinary Lean and IR-interpreter behavior from generated WASM behavior.
- [x] Define the initial direct-handoff judgment.
- [x] Classify all twenty-two tracked source release sites.
- [x] Enforce the judgment before IR extraction and report its result.

## 2026-07-13: Direct release handoff checker

`LeanExe/Extract/ReleaseCheck.lean` now validates every explicit source release after the first extraction pass computes helper fresh-result summaries and before the accepted IR reaches WASM emission.  It accepts recursive constructors, array literals and replication, helper results whose owner offset is fresh, and the exact owner-zero `setIfInBounds values.size` form.  Each accepted judgment records its declaration, source binding, and provenance for `ownership-report`.

The checker rejects later use, repeated release, direct aliases, container escape, return escape, parameter ownership, branch-selected roots, conditionally owned array operations, structure fields, loop-carried roots, and helper results without a fresh-owner summary.  Diagnostics name the declaration and released expression, then state the known provenance and rejection reason.  Eight reduced source fixtures cover use after release, double release, aliasing, container escape, return escape, parameter consumption, an interprocedural alias, and an out-of-bounds update over a possibly owned helper parameter; the existing branch, pop, and reverse fixtures cover unresolved conditional provenance.

The audit required one source correction and two explicit deferrals.  `JsonTreeCommand.insertOwned` no longer contains a redundant source release because its `Array.foldl` caller already uses the compiler's proved accumulator-replacement release rule, preserving the tree WASI pipeline.  `JsonMergeTreeCommand.makeMergedTree` now rejects when a source root has entered the heap-valued merged binding, and `JsonGcTreeRewrite.transform` rejects when `runRoundsFuel` releases the `tree` field of loop-carried state; both sources remain requirements for later retained-handoff and field-sensitive analysis.

Focused verification passed 781 accepted core cases, 45 exact rejections, 13 traps, 10 ownership-report cases, and 38 reference-counting cases.  The reference-counting suite retains Wasmtime checks for direct fresh arrays, recursive roots, fresh helper results, shared retained children, and an owner-zero array release.  The WASI suite passed 33 program cases, two traps, nine rejections, and sixteen compiles after the merge assertion was corrected to check its heap-bearing escape reason.

- [x] Validate every reachable explicit release before final extraction.
- [x] Report accepted source judgments through `ownership-report`.
- [x] Add exact rejection fixtures for every initial unsupported shape.
- [x] Preserve the JSON tree pipeline through compiler-managed fold cleanup.
- [x] Run the complete execution, WAT, and Talos gates.

The complete execution gate passed 114 report-classification cases, 10 ownership-report cases, 781 accepted core cases, 45 rejections, 13 traps, 7 leak-accounting cases, 38 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, 4 integer-map cases, 48 JSON cases, 33 WASI program cases with 2 traps, 9 rejections, and 16 compiles, 63 self-emitted LEB128 cases, 301 standard-Lean comparisons, 58 IR comparisons, and 56 fuzz cases.  The WAT gate passed nine entries after replacing the deferred `JsonGcTreeRewrite.transform` matrix entry with the accepted `JsonTypedDecode.transform`; every parsed WAT artifact matched the directly emitted binary byte-for-byte.  The Talos gate compared all fourteen regenerated WASM and WAT artifacts with their checked-in proof inputs and rebuilt the aggregate `Project` library without an artifact mismatch or proof error.

## 2026-07-13: Single-evaluation array search matches

`Array.findIdx?`, `Array.find?`, and `ByteArray.findIdx?` now bind one encoded search result whose zero value means missing and whose positive value is the found index plus one.  Extraction derives the public `Option` tag and payload from that local, and structured match results use a statement-level branch before result slots are assigned.  CLOB `cancel` therefore scans the order array once and reuses the recorded index in `eraseIdx!`.

The reduced fixtures cover a scalar helper result, unused structure fields that contain trapping array reads, structure results, fresh array results, and an executed trapping predicate.  The heap fixture allocates the literal search array and one branch result, releases the returned root once, and records `2 0 1 1` for allocation, retain, release, and free counts on both found and missing inputs.  Standard Lean and Wasmtime agree on both scalar branches and both heap-result branches, while the scalar cases also agree with the IR interpreter.

The CLOB WAT shrank from 23,020 bytes to 19,838 bytes in the reviewed text rendering.  The diff removes two full predicate scans, introduces one encoded-index local, and preserves the erase allocation, header stores, and two copy loops with local renumbering.  The checked Talos artifact remains unchanged, so `tools/check-talos-clob-cancel.sh` reports the expected byte mismatch until the complete cancel proof in the next phase accepts the regenerated artifact.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness` completed successfully.
- [x] `node test/matched_values.js` returned `checked 4 matched-value IR cases and 1 WAT scan case`.
- [x] `node test/core_correctness.js` returned `checked 791 accepted, 45 rejected, and 14 trapped cases`.
- [x] `node test/refcount.js` returned `checked 40 refcount cases` with both matched-array branches at `2 0 1 1`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 309 standard Lean comparison cases` and `checked 62 IR interpreter comparison cases`.
- [x] Review of `/tmp/clob-cancel-before.wat` and `/tmp/clob-cancel-after.wat` accounted for every removed scan and retained found-branch block.
- [x] `tools/check-talos-clob-cancel.sh` stopped at the expected proof-input byte comparison before rebuilding the stale proof.

## 2026-07-13: Single-scan cancel proof checkpoint

The CLOB scan lemma now follows the single generated loop and records an encoded first-match index.  Its absent case returns zero after reaching the array length, while its found case returns `UInt64.ofNat i + 1` with the matched order fields still loaded.  The list bridge continues to identify the first matching source index through `List.findIdx?`.

The existing `cancel_notFound` theorem retains its quantified order list, absent-identifier premise, borrowed input pointer, status-three result, and exact store equality.  Its proof now invokes the scan lemma once and follows the generated not-found helper call directly.  The transactional artifact update replaced the WASM, WAT, and generated Talos model only after the theorem rebuilt successfully.

Checks run:

- [x] `lake build Project.ClobCancel.Spec` completed 3,009 proof jobs.
- [x] `tools/check-talos-clob-cancel.sh --update` regenerated the three proof inputs and rebuilt `Project.ClobCancel.Spec`.
- [x] The checked WASM size changed from 2,216 bytes to 1,930 bytes after removal of the duplicate scans.

## 2026-07-13: Complete single-scan cancel theorem

`Project.ClobCancel.Spec.cancel_found` proves the allocating branch for every
represented order array whose input and fresh result occupy disjoint,
nonwrapping memory regions.  The proof follows the inline bump allocator,
checks all six header stores, writes the output length, and proves both word
copy loops with decreasing measures.  The final list argument converts the
copied prefix and suffix into `OrdersAt st' (g0 + 48) (os.eraseIdx i)`.

`Project.ClobCancel.Spec.cancel_correct` selects the missing or found theorem
from the single `idIdx` result.  Its missing branch returns the borrowed input
pointer and exact unchanged store without allocator assumptions.  Its found
branch returns a refcount-one array, advances the heap top by the exact object
size, increments the allocation counter once, preserves all other globals and
pages, and leaves every byte below the old heap top unchanged.

The focused proof build completed 3,009 jobs without a warning.  A repository
scan found no `sorry`, admitted theorem, new axiom, or diagnostic trace in the
CLOB cancel proof directory.  The cancel artifact check compared regenerated
WASM and WAT with the checked proof inputs and rebuilt the theorem; the later
aggregate Talos and complete execution gates also passed.

- [x] Prove the inline allocator and six header stores.
- [x] Prove the prefix and suffix copy loops.
- [x] Prove exact `eraseIdx` contents and output ownership.
- [x] Combine the found and missing branches in `cancel_correct`.
- [x] Run `tools/check-talos-clob-cancel.sh`.
- [x] Run the aggregate proof and complete execution gates.

## 2026-07-13: Quote artifact repair and phase gates

The statement-level branch materialization introduced for matched structure values also changed the CLOB quote artifact.  Its six `quoteStep` result fields now receive values inside one selected statement branch instead of projecting six independently guarded expressions.  The first aggregate artifact check found this omitted Phase 2 consequence, and the transactional `--update` command restored the checked inputs when the existing proof did not accept the regenerated program.

The repaired `Project.ClobQuote.Step.func9_spec` follows the selected statement branch and retains the same source-level result.  The focused quote proof and specification build pass, and `tools/check-talos-clob-quote.sh` compares the regenerated WASM and WAT with the checked inputs before rebuilding them.  The WASM artifact decreased from 2,853 bytes to 2,047 bytes because the generated function no longer repeats the branch condition for each field.

The aggregate `tools/check-talos.sh` gate compared all fourteen artifacts and completed 3,048 build jobs without an artifact mismatch or proof error.  The build reports existing linter warnings in older handwritten proofs, which remain Phase 6 work.  `node test/run_all.js` passed 114 report-classification cases, 10 ownership-report cases, the JavaScript execution guard, 791 accepted cases, 45 rejections, 14 traps, four matched-value IR cases, one WAT scan, seven leak-accounting cases, 40 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, four integer-map cases, 48 JSON cases, 33 WASI program cases, 63 self-emitted LEB128 cases, 309 standard-Lean comparisons, 62 IR comparisons, and 56 final cases.

## 2026-07-14: CLOB `findBest` branch gate

The Phase 4 test review found that `LeanExe/Examples/ClobTest.lean` was absent from the complete test runner and that the standard-comparison matrix contained no CLOB entries.  Earlier journal text claimed six `scenario` comparisons and one `cancel` comparison, but the tracked matrix no longer contained those cases.  The source guards therefore ran only when a developer named their module directly, and the full gate did not provide the claimed differential coverage.

The runner now builds `LeanExe.Examples.ClobTest`, whose direct `findBest` guards cover empty input, a same-side maker, a same-trader maker, a maker outside the limit price, an eligible maker after a rejected prefix, better and worse candidates, equal-price FIFO ties, and both taker sides.  Five public-ABI comparisons pass arrays of five-word `Order` structures and a scalar `Order` argument to the exported function, then compare its `Option Nat` result with ordinary Lean.  The comparison code reuses the existing ABI layout functions and adds no source wrapper or third-party dependency.

`lake build LeanExe.Examples.ClobTest` completed three jobs with all guards accepted.  The focused public-ABI command matched the buy-side replacement case, and the complete standard-comparison matrix passed 314 standard-Lean cases and 62 IR cases.  The five added cases explain the standard total's increase from 309 to 314; the IR total is unchanged because its interpreter does not accept heap-backed public ABI arguments.

## 2026-07-14: Shared CLOB order-array model

The `findBest` artifact confirmed that quote, cancel, and the remaining CLOB proofs consume the same five-word order-array representation.  `Project.Clob` now owns `OrderL` and `OrdersAt`, while quote retains its fold model and cancel retains its identifier scan and allocation arithmetic.  This completes the first Phase 5 reuse item after three independent artifacts established the shared statement.

The move changes no definition body or theorem statement after namespace resolution.  `lake build Project.ClobQuote.Spec Project.ClobCancel.Spec` rebuilt the shared module, quote step and specification, cancel scan, and complete cancel specification in 3,010 jobs.  Both proofs remain accepted without editing their generated `Program.lean` files or checked WASM and WAT inputs.

## 2026-07-14: CLOB `findBest` proof scaffold

The `clob_find_best` Talos case now pins the compiled `LeanExe.Examples.Clob.findBest` export.  The artifact is 3,462 bytes of WASM and 42,412 bytes of printed WAT, with the public wrapper at function 8, the fuel loop at function 7, scalar decision helpers at functions 1, 4, 5, and 6, and runtime functions at indices 9 through 12.  The runtime definitions match the shared allocator, reset, retain, and index-parametrized release definitions by reduction.

`Project.ClobFindBest.Model` restates opposite-side selection, crossing, eligibility, better-price comparison, fuel recursion, and the public two-word `Option Nat` result.  `Project.ClobFindBest.Helpers` proves the four scalar helpers over arbitrary orders and stores, including the short-circuit path that skips the crossing call when side or trader eligibility fails.  The helper build completed 3,006 jobs without a warning after unused simplification arguments were removed.

`tools/check-talos-clob-find-best.sh --update` generated the WASM, WAT, and decoded model transactionally and built the temporary specification module.  The case belongs to the aggregate artifact script and proof-library import, but this checkpoint does not count it as a verified artifact because the fuel-loop and export theorems remain.  The next increment proves the exact `findBestL` result for every represented order array before updating the theorem inventory.

The checked artifact comparison passed after generation.  `lake build Project.Runtime.Checks Project` then completed 3,053 jobs, including the new runtime pins and aggregate proof-library import.  The build reported only warnings that predate this proof directory.

## 2026-07-14: Complete CLOB `findBest` proof

`Project.ClobFindBest.Loop.func7_spec` proves termination and the exact `findBestL` result for every represented order array, taker, and input length below `2^32`.  Its postcondition covers all five generated result branches and preserves the complete store.  `Project.ClobFindBest.Spec.findBest_correct` connects the public six-argument ABI to the source two-word `Option Nat` result with the same store guarantee.

`Project.ClobFindBest.Spec.findBestL_best` proves the source search's economic property for a valid taker side.  A successful result is in bounds and eligible, no eligible candidate has a better price, and an equal-price eligible candidate cannot precede the returned index.  The proof derives the result from a prefix invariant shared with the exact fuel-recursive model.

The checked artifact remains 3,462 bytes of WASM and 42,412 bytes of WAT.  The generated loop calls function 5 at four syntactic sites and performs the price comparison inline; function 6 remains present in the compiled module but function 7 does not call it.  The proof follows those emitted instructions, leaves `Program.lean` unchanged, and adds no axiom, admission, or third-party dependency.

- [x] `lake build Project.ClobFindBest.Spec` completed 3,008 jobs without a warning in the `findBest` modules.
- [x] `tools/check-talos-clob-find-best.sh` matched the checked WASM and WAT and rebuilt the specification.
- [x] The focused artifact check reported only the pre-existing `AsciiDigits.lean` unused-argument warning scheduled for Phase 6.

## 2026-07-14: CLOB `postOnly` branch gate

The existing source guards covered duplicate identifiers, invalid sides, zero quantities, crossing orders, and successful appends, but omitted zero identifiers and zero traders.  They inspected status and selected book lengths rather than the complete `OpResult`.  The standard/WASM comparison matrix contained no `postOnly` case.

The branch gate now checks all five `validOrder` failure paths, the `findBest` crossing result, and the successful append result.  Each comparison passes an order array and taker through the public ABI, then compares status, every returned order field, and the empty trade array with ordinary Lean.  The result layout and serializers use the existing structured ABI test framework and add no source wrapper or dependency.

`lake build LeanExe.Examples.ClobTest` accepted every source guard, including the two new validity cases.  `node tools/compare-standard.js --self-test` passed 321 standard-Lean cases and 62 IR cases, with all seven `postOnly` comparisons succeeding.  The standard total increased from 314 to 321, while the IR total remains unchanged because the interpreter does not accept heap-backed public ABI arguments.

## 2026-07-14: CLOB `postOnly` proof scaffold

The `clob_post_only` case now pins the compiled `LeanExe.Examples.Clob.postOnly` export.  The artifact is 5,915 bytes of WASM and 70,775 bytes of WAT, with the public wrapper at function 17 and runtime functions at indices 18 through 21.  The runtime functions match the shared allocator, reset, retain, and index-parametrized release definitions by reduction.

`Project.ClobPostOnly.Model` states the five validity conditions and the invalid, would-cross, and appended source outcomes over the shared order representation.  Invalid and would-cross results borrow the input book and allocate one empty trade array.  The successful result allocates both the appended book and an empty trade array, so its artifact theorem requires a separate two-allocation postcondition.

`tools/check-talos-clob-post-only.sh --update` generated the proof inputs and decoded model transactionally, then built the placeholder specification.  `lake build Project.Runtime.Checks Project` completed 3,057 jobs with the new runtime pins and aggregate import.  The build reported existing linter warnings outside the new proof directory, and the case does not enter the verified theorem count until its input-generic specification is complete.

## 2026-07-14: CLOB `postOnly` helper proofs

`Project.ClobPostOnly.SearchHelpers` proves side selection, crossing, eligibility, and better-price behavior at the new artifact's function indices.  The instruction bodies match the earlier `findBest` helpers apart from their indices and internal call targets.  Each theorem ranges over arbitrary scalar orders and preserves the store.

`Project.ClobPostOnly.ValidOrder.func5_spec` proves that the generated identifier scan returns one exactly when an order with the requested identifier occurs.  Its loop invariant records a clean processed prefix, reads all five fields through the shared `OrdersAt` predicate, and terminates by decreasing the unprocessed length.  `func6_spec` combines that result with nonzero identifier, nonzero trader, valid side, and nonzero quantity in the emitted short-circuit order.

`lake build Project.ClobPostOnly.SearchHelpers` completed 3,006 jobs, and `lake build Project.ClobPostOnly.ValidOrder` completed 3,008 jobs.  Both focused targets build without a warning in the new proof files.  The proofs add no source wrapper, generated-file edit, axiom, or admission.

## 2026-07-14: CLOB `postOnly` search proof

`Project.ClobPostOnly.FindBest.func12_spec` proves termination and the exact source `findBestL` result for every represented order array and taker.  It instantiates the established prefix invariant at function 12 and calls the new artifact's eligibility helper at function 10.  All five generated result branches preserve the complete store.

`Project.ClobPostOnly.FindBestWrapper.func13_spec` reads the array length, checks the fuel addition for overflow, and invokes function 12 with an empty initial result.  It returns the same two-word option ABI as the standalone `findBest` export and preserves the store.  The separate wrapper file keeps later wrapper edits from forcing another elaboration of the 1,005-line loop proof.

`lake build Project.ClobPostOnly.FindBest` completed 3,007 jobs in 218 seconds.  The wrapper target then completed 3,008 jobs in five seconds.  Both builds produced no warning, and the adaptation leaves the generated `Program.lean` unchanged.

## 2026-07-14: Shared fixed-array allocation predicate

`Project.Clob` now defines the byte count and six-word allocation header for a fixed-width array.  The predicate records the runtime magic word, reference count, byte capacity, array kind, element stride, and owner mask at their exact offsets from the returned data pointer.  Order and trade arrays can specialize one statement instead of defining separate header layouts.

The complete `cancel` theorem now defines `FreshOrderArrayAt` as the stride-five specialization of the shared predicate.  Its byte-count definitions remain local because its arithmetic proof depends on their direct normal form, while later artifacts can use the generic count from the start.  The theorem statement and generated artifact remain unchanged.

`lake env lean Project/ClobCancel/Spec.lean` rebuilt the complete found and missing proof after rebuilding `Project.Clob`.  The target passed without an error or warning.  This checkpoint adds no axiom, admission, dependency, or generated-file edit.

## 2026-07-14: Shared CLOB memory frame theorem

`Project.Clob.OrdersAt.frame` preserves a represented order array across writes above a stated heap boundary.  Its hypotheses require an unwrapped 32-bit input extent, the input below the boundary, unchanged page count, and byte equality below that boundary.  The proof derives every header and field read with the common `read64_congr` lemma and preserves each memory bound through page equality.

The invalid and crossing `postOnly` branches can now state both the borrowed input pointer and its exact source contents after allocating the trade array.  Later matching proofs can apply the same theorem when fresh result arrays occupy memory above their input books.  This removes five-field readback proofs from each allocation branch.

`lake env lean Project/Clob.lean` checked the new theorem without an error or warning.  The theorem uses the existing memory model and adds no axiom or dependency.  No artifact input changed.

## 2026-07-14: CLOB `postOnly` allocation vocabulary

`Project.ClobPostOnly.Allocation` specializes the shared fixed-array definitions for stride-five orders and stride-four trades.  `FreshTradeArrayAt` combines the common owned-array header with the emitted zero length at the returned data pointer.  The order byte count uses the generic fixed-width calculation from the start.

The module also proves the exact results of functions 14, 15, and 16.  These helpers return would-cross status two, success status zero, and invalid status one while preserving the store.  The public wrapper proof can consume their behavior through the call rule.

`lake build Project.ClobPostOnly.Allocation` completed 3,005 jobs without an error or warning.  The generated program remains unchanged.  The module adds no axiom, admission, or dependency.

## 2026-07-14: CLOB `postOnly` invalid branch

`Project.ClobPostOnly.Invalid.postOnly_invalid` proves the public function-17 path for every represented book and every order that fails `validOrderL`.  The export returns status one, the borrowed input-book pointer, and a fresh empty trade array at the old heap top plus 48 bytes.  The theorem re-establishes the exact input-book contents through `OrdersAt.frame` after the allocation writes.

The proof follows the emitted free-list loop, bump allocation, page check, six header stores, zero-length store, and allocation-counter update.  Its empty-free-list and fit hypotheses select the no-growth bump path.  The postcondition records the stride-four header, reference count one, eight-byte capacity, zero length, unchanged page count, advanced heap top and allocation count, and byte equality below the old heap top.

`lake env lean Project/ClobPostOnly/Invalid.lean` checked the theorem without an error or warning.  A targeted Lake build produced the module object after rebuilding invalidated shared dependencies.  The proof contains no axiom, admission, generated-file edit, or additional dependency.

## 2026-07-14: CLOB `postOnly` crossing branch

`Project.ClobPostOnly.Crossing.postOnly_crossing` proves function 17 for every valid order whose source `findBestL` result is `some maker`.  The proof composes the exact validity and search theorems at functions 6 and 13, then selects the generated would-cross branch.  The public result contains status two, the borrowed input book, and one owned empty trade array.

The allocator postcondition matches the invalid branch: heap top advances by 56 bytes, allocation count advances once, and page count remains fixed.  The fresh array has reference count one, eight-byte capacity, array kind two, stride four, owner mask zero, and length zero.  `OrdersAt.frame` proves that the seven allocation writes preserve the represented input book.

Rebuilding the shared `FindBest` theorem after the CLOB model edit completed 3,007 jobs in 325 seconds.  `lake build Project.ClobPostOnly.Crossing` then completed 3,012 jobs in 24 seconds without an error or warning.  The crossing theorem adds no axiom, admission, dependency, or generated-file edit.

## 2026-07-15: Compiler Workspace Upgrade to Lean 4.31

The root `lean-toolchain` now pins Lean 4.31.0, matching the Talos proof workspace.  Compatibility edits use Lean 4.31's direct `Nat` comparisons, proof-bearing `ByteArray.get`, nested error contexts, and generated recursion declarations.  The upgrade adds no dependency and leaves the public compiler commands unchanged.

Lean 4.31 places equation-compiled natural-number recursion in a generated `<declaration>._f` helper, and structural `brecOn` helpers can apply `_f` to captured arguments before the recursive argument.  Extraction now recognizes that shape, instantiates and beta-reduces the helper, and traverses the helper dependencies when building the accepted declaration set.  The release checker validates releases inside `_f` under the source declaration name, which restores rejection of a loop-carried structure-field release in `JsonGcTreeRewrite.runRoundsFuel`.

Repository instructions now require one resource-limited user scope around every Lean, Lake, compiler, or compiler-spawning command.  The scope sets `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and a command-specific timeout.  Lake 5.0.0 exposes no job-count option, so the CPU quota limits Lake and all child processes to one core and concurrent Lean processes remain prohibited.

The complete root gate passed after a clean build.  It reported 114 classification cases, 10 ownership-report cases, 791 accepted cases, 45 rejections, 14 traps, 4 matched-value IR cases, 1 matched-value WAT assertion, 7 leak-accounting cases, 40 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, 4 integer-map cases, 48 JSON cases, 33 WASI program cases with 2 traps, 9 rejections, and 16 compiles, 63 self-emitted LEB128 cases, 321 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases.  The clean build exposed five modules that the complete runner consumed without building explicitly, so `test/run_all.js` now names them in its initial Lake build.  Removing the obsolete `hsize` simplification argument also leaves the root build free of warnings.

The WAT round-trip gate passed all nine entries.  Compiler-only comparison against the sixteen checked Talos inputs matched fifteen WASM and WAT pairs; `assoc_list` differs because the Lean 4.31 form removes eight WAT lines that normalize an already Boolean result before comparing it with one.  Disk cleanup removed the proof cache, and the in-progress `postOnly` proof has uncommitted work, so this migration neither updated proof inputs nor ran the proof build; `assoc_list` regeneration and proof validation remain required before the toolchain artifact gate passes.

- [x] Pin the root compiler workspace to Lean 4.31.0.
- [x] Support Lean 4.31 recursion helpers and release validation.
- [x] Constrain every Lean process by memory, CPU, I/O priority, and timeout.
- [x] Run the complete root execution and WAT gates.
- [x] Regenerate and prove the changed `assoc_list` artifact after proof work resumes.

## 2026-07-15: CLI Failure Interface

`LeanExe.CLI` now classifies handled failures at explicit operation boundaries.  Command-use and bound errors return status two, source and project-input rejections return three, I/O failures return four, and encoder invariants or exceptions outside those boundaries return five.  Each stderr record names the category and command, includes available module, entry, and output-path context, and retains the detailed extractor or operating-system message.

`test/cli_errors.js` runs the executable as a child process and checks malformed command shape, nonnumeric and excessive bounds, a missing module, a missing entry, a wrong WASI entry type, an unsupported declaration, a reserved export name, a failed output write, and help output.  The test also requires empty stdout on failure, the documented status, contextual stderr, no ANSI escape, and no `uncaught exception` prefix.  The complete constrained root gate passed 114 classification cases, 10 ownership-report cases, 9 CLI failure cases, 791 accepted cases, 45 rejections, 14 traps, 40 reference-counting cases, 321 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases; the nine-entry WAT round-trip also passed.

This work leaves the Talos proof workspace unchanged.  Existing proof support already includes `read_frames`, `OrdersAt`, `OrdersAt.frame`, and `FreshFixedArrayAt`, which cover repeated read-over-write, represented-order, framing, and fixed-array-header obligations.  When proof work resumes, the next reuse review should compare the completed cancel copy loops with the in-progress `postOnly` append branch and add a shared theorem only if both need the same combined allocation, content, and frame postcondition; a new tactic should require repeated address or invariant forms that the current `read_frames` tactic does not solve.

- [x] Define one public CLI failure status scheme.
- [x] Add process-level tests for every required failure path.
- [x] Preserve successful compiler output and WAT round trips.
- [ ] Review cancel and `postOnly` copy obligations together when Talos proof work resumes.

## 2026-07-15: Node and `wasm-tools` Pins

The repository now pins Node 24.13.0 in `.node-version` and `wasm-tools` 1.251.0 in `.wasm-tools-version`.  Node generates test runners and compares process output, while `wasm-tools` prints the WAT that Talos decodes, so the gates reject an unreviewed version change.  The pins add no package manager, library, or downloaded dependency.

`tools/check-node-version.js` compares `process.version` with the Node pin before `test/run_all.js` starts a build, and the runner uses that process's `execPath` for every Node child test.  `tools/check-wasm-tools-version.sh` validates the executable selected through `WASM_TOOLS`, `PATH`, or `$HOME/.cargo/bin`, and both `tools/check-wat.sh` and `tools/check-talos-case.sh` invoke it before generating an artifact.  A mismatch names the expected version, first observed version line, and selected executable without ANSI output.

The Node syntax, pin, and `execPath` checks passed with `v24.13.0`, and the `wasm-tools` success and deliberate mismatch paths returned the expected statuses and messages.  The version-enforced WAT gate checked `wasm-tools 1.251.0`, rebuilt `lean-wasm` under the repository resource limits, and matched all nine binary and text entries.  No Talos proof command ran, and no checked proof input changed.

- [x] Record and enforce Node 24.13.0.
- [x] Record and enforce `wasm-tools` 1.251.0.
- [x] Run the version-enforced WAT gate.

## 2026-07-15: Wasmtime Archive Verification

The [official immutable Wasmtime 44.0.0 release](https://github.com/bytecodealliance/wasmtime/releases/tag/v44.0.0) publishes SHA-256 digests for every release asset.  `tools/download-wasmtime.sh` now records the CLI and C API archive digests for `aarch64-linux` and `x86_64-linux`.  A version or platform without built-in digests requires explicit `WASMTIME_CLI_SHA256` and `WASMTIME_C_API_SHA256` values before the script creates its destination directory or contacts a release server.

The downloader verifies a cached archive before reuse and verifies a new `.part` file before replacing the cache or extracting it.  A corrupt cached file triggers a replacement download, while a corrupt downloaded file produces a nonzero failure and never reaches extraction.  The script requires `sha256sum`, preserves its two stdout environment assignments, and sends recovery and failure details to stderr.

The cached aarch64 CLI and C API archives matched the official digests `294cae921fb88cbbcb60a914eaaaf313df3249d718609afb5804186b3f1912f5` and `6f1fb604f6d3f307f2d093bdc18e9781c85692e17c2360f5975875817adc34ab`.  The official x86-64 CLI and C API digests are `52eba06fe9f4364aa6164a4a3eafb2ca692ba9a756cbe8137b5574871f8cbfc8` and `e193aa35338637d84f172323a909cebb907c14c55b5a4b5bdbf89f5cd0b89c81`.  An isolated `file://` fixture confirmed wrong-cache detection, verified replacement, extraction, and symlink creation without modifying the repository cache.

- [x] Record all four official Wasmtime 44.0.0 Linux archive hashes.
- [x] Verify cached and downloaded archives before extraction.
- [x] Reject unchecked version and platform overrides.
- [x] Test corrupt-cache replacement in an isolated local fixture.

## 2026-07-15: Separate Talos Setup and Gate Output

The aggregate Talos driver now checks all sixteen WASM and WAT pairs before it consults the proof workspace.  Each case runs in a new `--artifacts-only` mode that suppresses successful root Lake output and prints one matched-case record.  The first byte mismatch therefore stops the gate before dependency builds or proof warnings can obscure its case name and file paths.

The default aggregate then runs `lake --no-build` for `Project`, with informational and warning output suppressed.  A missing or stale target produces a short Lake error list and an instruction to run `tools/setup-talos.sh`.  That setup command owns the potentially large dependency and proof build, while ordinary per-case checks retain their focused proof build and transactional `--update` behavior.

Bash syntax checks, argument-conflict checks, and `git diff --check` passed.  The constrained aggregate artifact test matched `gcd` and stopped at the known Lean 4.31 `assoc_list` WASM difference at byte 222.  A constrained no-build probe reported four stale proof targets in 1.3 seconds without compiling them; no hard Talos proof ran, and the current `postOnly` work remained unchanged.

- [x] Add artifact-only per-case checks.
- [x] Compare every aggregate artifact before proof output.
- [x] Give cold and stale proof builds a separate command.
- [x] Preserve per-case update rollback and proof validation.

## 2026-07-15: Lean 4.31 `assoc_list` Artifact

The refreshed `assoc_list` artifact removes one eight-instruction Boolean normalization after the identifier comparison.  The deleted sequence compared an existing zero-or-one result with zero, inverted that comparison, rebuilt zero or one through a conditional, and then compared the rebuilt value with one.  Lean 4.31 leaves the original zero-or-one result in place for the final comparison.

The WASM file shrank from 3,552 to 3,539 bytes, and the WAT and generated Talos model each lost the corresponding eight instructions.  The handwritten `Project.AssocList.Spec` file required no edit and rebuilt successfully after transactional regeneration.  The refreshed WASM, WAT, and model SHA-256 hashes are `6b356640062b5977acaf5459a6d3f8c3f1184c1a3e442b963c54e7a1d3a5a1de`, `231aa47360d41c24019b4447391a2d3d72f3c9ee11d6cc450238cf0e41ad48cd`, and `b5375bb25bec502a9d3291df2fea8f2b691f510df3f914e08582fedd581637a0`.

The constrained per-case update completed 3,006 Lake jobs in 18 seconds.  The constrained aggregate artifact-only gate then matched all sixteen WASM and WAT pairs in eight seconds.  Both commands ran with the repository memory, CPU, priority, and timeout limits, and neither command changed the in-progress `postOnly` proof files.

- [x] Review the emitted instruction difference.
- [x] Regenerate the checked WASM, WAT, and Talos model.
- [x] Rebuild the existing input-generic theorem.
- [x] Match all sixteen artifacts against Lean 4.31 output.

## 2026-07-15: Proof Maintenance and Fixed-Array Framing

Stored Lean traces contained 267 warning records across twelve handwritten proof modules, including duplicate records for unreachable tactics.  Focused edits removed the warning in `FoldSum.Spec`, four interface-binder warnings in `LebU32.Copy`, and all seventeen warnings in `Runtime.Tree` and `Runtime.TreeSpec`.  Constrained `--wfail` builds completed in 3.2 seconds for `Runtime.Tree`, 13 seconds for `Runtime.TreeSpec`, and 2.8 seconds for `LebU32.Copy` after a separate three-second dependency rebuild, without a warning in any checked target.

One Lake invocation named `Validate`, `FoldSum`, and `SharedPair` as separate targets.  Lake started two Lean children concurrently even though their common cgroup limited the process tree to one CPU and six gigabytes, which violated the repository rule against concurrent Lean processes.  I interrupted that build, restored the unverified `Validate` and `SharedPair` edits, confirmed their diffs were empty, and used exactly one target in every later Lake invocation.

An isolated `SharedPair.Spec` warning-only build reached its 30-minute timeout, and an isolated `LebU32.Iter` warning-only build reached its 15-minute timeout.  Host process checks showed one Lean child in each scope, but memory pressure left little CPU progress during the elapsed time.  Both edits were restored exactly, and warning-only work on `Iter`, `NegIter`, `SharedPair`, `PushSize`, `PushTwice`, `PairFree`, and `BoxFree` remains deferred until a substantive theorem change or smaller module boundary justifies the elaboration cost.

`Project.Clob.FreshFixedArrayAt.write64_data` proves that a 64-bit write in the data region preserves the six fixed-array header words.  `ClobCancel.Spec` now applies this theorem at two copy-write sites, replacing twenty-seven lines of repeated framing proofs, while the untracked `ClobPostOnly.Append` proof contains the third matching use site and remains untouched.  Constrained `--wfail` builds completed in 3.3 seconds for `Project.Clob` and 41 seconds for `Project.ClobCancel.Spec`, with one Lean child and no warning in either checked target.

The final process check found no Lean or Lake process, and `LebU32.Iter` matched its committed contents after restoration.  The working tree still contains only the pre-existing modified `ClobPostOnly.Spec`, untracked `ClobPostOnly.Append`, and nested untracked `leanclob` repository.  No generated model, checked WASM, checked WAT, or current `postOnly` proof file changed during this maintenance.

## 2026-07-15: Recursive Public-ABI State

The expanded CLOB comparison matrix exposed a compiler error in exported natural-number recursion.  The public ABI represents a heap array by its data pointer, while the internal recursive representation carries its owner and data pointer in separate slots.  The old lowering assigned internal recursive slots positionally from public parameters, so a nested `MatchState` corrupted its book, trades, or remaining order after the first iteration.

Exported recursion now initializes separate internal carried locals from the public ABI and materializes a fresh aggregate recursive argument once before assigning its component slots.  Loop-owner trackers start at zero because function inputs are borrowed, record allocations created inside the loop, retain ownership when the next state carries the same allocation, and release an owned value when no next owner slot retains it.  Materialization remains limited to exported ABI conversions and aggregate top-level carried types, preserving the established direct lowering for byte arrays, scalars, and nonaggregate arrays.

A reduced `RecArrayState` fixture exercises two recursive iterations and checks the public owner-and-pointer conversion.  The reference-counting suite now passes 41 cases, including a two-iteration case with three allocations, no retain, one release, and one free.  The standard comparison matrix passes 340 source comparisons and 62 IR comparisons, including seven `postOnly`, five `matchFuel`, six `limit`, five `market`, and two `depth` cases.

The complete root runner passed once during implementation with 791 accepted cases, 45 rejections, 14 traps, and the full supporting test set.  After the final materialization scope was narrowed, focused compiler, reference-counting, differential, WAT, and sixteen-case Talos artifact checks passed against the final source.  The narrowing restored byte-identical `validate` and `leb_u32` artifacts and changed no checked proof input.

The default Talos gate matched all sixteen WASM and WAT pairs, then used its no-build proof check.  Seven proof targets were stale: `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, `Project.LebU32.NegIter`, `Project.ClobFindBest.Model`, `Project.ClobPostOnly.Allocation`, and `Project.Runtime.Checks`.  This result reports missing or outdated build objects after cache removal; it does not report a failed theorem.

## 2026-07-15: Flat Order Reconstruction

`Project.Clob` now defines `OrderL.word` and `orderWord` as the shared flat view of one five-word order record.  `OrdersAt.orderWord_eq` projects any represented order to that view, and `OrdersAt.ofFlatWords` reconstructs the structured predicate from an indexed word equality and indexed memory bound.  These lemmas isolate the record-layout arithmetic that both cancel and the in-progress append proof had repeated.

The cancel theorem now handles its copied prefix and shifted suffix through one arbitrary field index.  The shared constructor expands that result into the five field reads and their memory bounds, removing seventy-two lines while preserving the theorem statement.  Constrained warning-failing builds completed `Project.Clob` in 2.1 seconds and `Project.ClobCancel.Spec` in 35 seconds with one Lean process and no warning.

A new tactic would add no useful proof boundary at this point.  `omega` handles the index arithmetic, `simp` handles the five concrete field projections, and `read_frames` handles read-over-write obligations.  Another helper should follow only when the completed append or matching proof reveals a second stable copy-loop or allocation postcondition beyond the flat-word lemma.

## 2026-07-15: Process Failure Diagnostics

Several JavaScript test runners assumed that a failed `spawnSync` call always returned string-valued stderr and stdout.  A launch failure returns an `error` and can leave both output values undefined, so the diagnostic path threw a property-access exception before reporting the missing compiler executable.  `tools/run-process.js` now owns synchronous launch checking, command formatting, status and signal reporting, and safe collection of optional output.

The compiler, execution, ownership, differential, WASI, and host runners now use the shared helper.  A focused test checks a missing executable with `ENOENT`, a status-seven child with specific stderr, and a successful child with ignored output streams.  `test/run_all.js` runs this test before compiler work and invokes each of its five explicit Lake targets sequentially, removing the previous multi-target command that could start concurrent Lean children.

The complete root suite passed under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and a one-hour timeout.  It passed 3 process-error cases, 114 classifications, 10 ownership reports, 9 CLI errors, 791 accepted cases, 45 rejections, 14 traps, 41 reference-counting cases, 340 standard-Lean comparisons, 62 IR comparisons, and every remaining execution group.  Each Lake command named at most one target, and the run used the absolute compiler path inherited by every child test.

## 2026-07-15: Bounded Talos Cache Restoration

The proof cache was restored one target at a time after the shared CLOB model changed.  `Project.Runtime.Checks`, `Project.ClobPostOnly.Allocation`, and `Project.ClobFindBest.Model` completed in 1.3 to 1.7 seconds.  The deeper CLOB chain also rebuilt successfully: `ClobFindBest.Helpers` in 104 seconds, `ClobPostOnly.SearchHelpers` in 103 seconds, `ClobFindBest.Loop` in 206 seconds, `ClobPostOnly.FindBest` in 216 seconds, and the remaining model, wrapper, validity, invalid, crossing, and specification targets in 1.1 to 27 seconds.

`Project.ClobPostOnly.Append` contains 1,105 lines and one public theorem spanning roughly 870 lines after its local definitions.  Its constrained warning-failing build reached the twenty-minute timeout without a Lean diagnostic or output object.  The target combines the first allocator walk, the complete flat-word copy loop, five appended-order writes, structured `OrdersAt` reconstruction, and the second allocator walk in one elaboration unit.

`Project.Validate.Spec` reached a fifteen-minute constrained timeout without a diagnostic.  Earlier unchanged attempts had already established 30-minute and 15-minute limits for `Project.SharedPair.Spec` and `Project.LebU32.Iter`, with `Project.LebU32.NegIter` sharing the same monolithic iteration structure.  Rebuilding these unchanged targets would repeat measured work without improving the proof architecture.

The append proof needs separately compiled theorems for the first allocation and copy phase, the five-field order store and structured-book reconstruction, and the empty-trade allocation and final frame.  The shared `OrdersAt.ofFlatWords` theorem supplies the semantic boundary for the middle phase, while `FreshFixedArrayAt.write64_data` supplies its header frame.  The existing `omega`, `simp`, and `read_frames` tactics already discharge local normalization, so another tactic would not reduce the size of the elaborated store and instruction terms.

Repository instructions now prohibit retrying an unchanged target after a no-diagnostic timeout.  A later attempt must divide the proof or module, or add a verified lemma that reduces the term elaborated in the timed-out target.  The in-progress `ClobPostOnly.Spec` and untracked `ClobPostOnly.Append` files remained unchanged during cache restoration.

## 2026-07-15: Composed `postOnly` Append Proof

The successful append branch now composes four instruction-slice theorems instead of elaborating one 870-line proof.  `AppendOrderAlloc` proves the free-list scan, bump allocation, header writes, and empty copy invariant; `AppendOrderCopy` proves the flat-word loop against a prefix invariant; `AppendOrderFinish` proves the five order stores and reconstructs `OrdersAt`; and `AppendTrade` proves the empty trade-array allocation.  The public `postOnly_appended` theorem retains the exact return values, book contents, fresh-array predicates, page and global updates, and low-memory frame.

The split uses continuation-parametric statements for the first three phases.  Each theorem proves `wp` for `phaseProg ++ rest` and accepts the next phase through a semantic postcondition, which prevents `wp` simplification from expanding later instruction lists.  `FreshFixedArrayAt.write64_data`, generalized fixed-array memory initialization, `OrdersAt.ofFlatWords`, and the existing `read_frames` tactic discharge the repeated semantic obligations without a new tactic.

The generated successful branch ends before the enclosing function's three result loads.  An initial composition included those loads in `AppendTrade.appendTradeProg`, and a checked program comparison found one nested suffix of length 125 matching the first 125 instructions of the 128-instruction composition.  The trade phase now stops after setting result locals 31, 32, and 33, and its assertion records those values so `wp.imp` can prove the enclosing continuation.

Constrained warning-failing builds complete `AppendOrderCopy` in 2.3 seconds, `AppendOrderAlloc` in 6.3 seconds, `AppendOrderFinish` in 9.4 seconds, `AppendTrade` in 1.7 seconds, and the cleaned 229-line `Append` module in 14 seconds.  `Project.ClobPostOnly.Spec` then rebuilt the invalid branch in 37 seconds, the crossing branch in 45 seconds, and the aggregate module in 1.2 seconds.  Every command used the repository memory, CPU, I/O-priority, and timeout limits, and no Lean or Lake command ran concurrently.

- [x] Divide the successful append proof into compiled semantic phases.
- [x] Match each named instruction slice to the generated nested branch.
- [x] Build `Project.ClobPostOnly.Append` and `Project.ClobPostOnly.Spec` with `--wfail`.
- [ ] Compare the completed cancel and append copy invariants with the next matching update before generalizing a whole-loop theorem.

## 2026-07-15: `matchFuel` Artifact Registration

`matchFuel` is not reachable from the `postOnly` export, so its proof requires a separate byte-pinned artifact.  The accepted export has nine public `i64` parameters for fuel, the taker, two array pointers, and remaining quantity, and returns three `i64` values for the resulting book, trades, and quantity.  The temporary compiler artifact contains 6,881 WASM bytes, 95,874 WAT bytes, nineteen functions, and an exported body spanning roughly 1,850 WAT lines.

The new `clob_match_fuel` case follows the existing verifier layout.  It adds one empty Rust crate manifest, compiler-produced WASM and WAT inputs, the generated 3,871-line `Project.ClobMatchFuel.Program`, a handwritten specification shell, and a focused check script.  The shell compiles but contains no semantic theorem, so the documentation records sixteen completed specifications and one in-progress case.

The aggregate artifact gate matched all sixteen prior pairs before its proof-freshness check reported six stale modules.  Four are unchanged modules with recorded no-diagnostic timeouts: `Validate.Spec`, `SharedPair.Spec`, `LebU32.Iter`, and `LebU32.NegIter`; the other two are bounded CLOB dependencies, `ClobQuote.Step` and `ClobFindBest.Helpers`.  The unchanged timeout cases require proof division before another build, while the bounded CLOB dependencies can rebuild as later targets require them.

## 2026-07-15: `matchFuel` Source Model

The matching exports share a four-word trade layout, so `Project.Clob` now defines `TradeL`, `TradesAt`, and flat-word introduction and elimination theorems beside the existing order representation.  `Project.ClobFindBest.Model` exposes the bound on every successful search result, which the matching branches need before reading or replacing an order.  `Project.ClobMatchFuel.Model` follows the source recursion over list-backed books and trades while preserving `UInt64` arithmetic.

The model target passes a warning-failing constrained build in 2.2 seconds after its dependencies were current.  The shared additions also passed warning-failing builds when Lake rebuilt `Project.Clob` and `Project.ClobFindBest.Model`.  No generated program changed.

The partial-fill branch replaces one maker quantity while preserving every other order field.  `setQtyL_length` proves that this update preserves the book length, `setQtyL_eq_set` identifies it with a valid `List.set`, and `setQtyL_word` states the exact changed flat word.  The model passes a warning-failing constrained build in 1.3 seconds with these lemmas.

- [x] Define the shared trade value and memory representation.
- [x] Prove that a successful `findBestL` result is in bounds.
- [x] Define exact list-level book, trade, and remaining-quantity transitions.
- [x] Prove the generated scalar and search helpers for the new artifact.

## 2026-07-15: Embedded `findBest` Proof

Functions 1 through 9 in the matching artifact reproduce functions 0 through 8 in the standalone `findBest` artifact, with internal call indices increased by one.  The matching proof now covers the side, crossing, eligibility, and price helpers, the complete fuel loop, and the internal wrapper at their generated indices.  The loop uses the public `bestPrefixL_some_lt` theorem from the source model instead of retaining the copied private proof.

Warning-failing constrained builds complete the helper module in 102 seconds, the 992-line loop module in 203 seconds, and the wrapper plus specification shell in 6.1 seconds.  The loop theorem returns `optionVals (findBestL os taker)` for every represented order list and preserves the complete store.  The remaining exported proof can therefore treat the generated search call as one verified semantic step.

- [x] Prove the four pure search helpers at the matching artifact's indices.
- [x] Prove the embedded generated search loop against `findBestL`.
- [x] Prove the internal wrapper and import it from the specification shell.
- [ ] Divide the exported matching loop at its three early-exit branches.

## 2026-07-15: Zero-Fuel Matching Exit

The first exported-function theorem proves that zero public fuel returns the input book pointer, trade pointer, and remaining quantity without changing the store.  Its loop invariant records the relevant locals, the zero done flag, and the exact nine-parameter and seventy-six-local frame lengths.  The frame lengths let the final return suffix simplify local assignments without expanding the complete generated frame.

The warning-failing constrained build completes `Project.ClobMatchFuel.EarlyExit` in 19 seconds.  The proof selects the generated false branch after the fuel test, follows its break from the enclosing block, and proves the final three-value ABI exactly.  The same frame facts will support the zero-remaining and no-maker exits, which each enter the loop once before setting the done flag.

- [x] Prove the zero-fuel exit over the exact public ABI.
- [x] Prove the zero-remaining exit for nonzero fuel.
- [x] Prove the no-maker exit through the verified search wrapper.

The zero-remaining theorem passes a warning-failing constrained build in 46 seconds.  Its two-phase invariant uses the done flag as a natural-number measure and proves the generated re-entry decreases that measure from one to zero.  Both phases preserve the complete store and return the input state pointers and zero remaining quantity.

The no-maker theorem extends the invariant with the stable taker fields, the wrapper's zero argument, and the empty operand stack.  It calls the verified function-9 search theorem, reduces the `none` option ABI, and returns the input state without changing the store.  The complete early-exit module passes a warning-failing constrained build in 79 seconds.

## 2026-07-15: Fixed-Array Release Semantics

The generated `matchFuel` module's functions 15 through 18 are definitionally equal to the shared allocator, reset, retain, and release definitions.  `Project.Runtime.Checks` now pins those equalities, and its warning-failing constrained build completes in 2.2 seconds.  Function 18 therefore uses the module-generic runtime specifications instead of an artifact-specific copy of the release proof.

The existing release theorems did not cover the arrays used by matching.  `release_frees_fresh_raw` requires kind 0, while `release_frees_tree` models kind-1 slot objects; CLOB books and trades are kind-2 fixed arrays.  The runtime's kind-2 branch reads the array length, stride, and pointer mask, walks both dimensions, releases each masked field, and then adds the root to the free list.

`Project.Runtime.FixedArraySpec.release_frees_fixed_array_zero_mask` proves the shared kind-2 case used by CLOB arrays.  Two natural-number variants prove termination of the generated nested loops, and the zero mask proves that the walk neither reads element words nor calls release recursively.  The theorem returns the exact refcount write, free-list link, release and free counter increments, and unchanged remaining globals; its warning-failing constrained build completes in 7.9 seconds.  `Project.ClobMatchFuel.Allocation.func18_frees_fixed_array_zero_mask` specializes the theorem to the generated module and passes a warning-failing constrained build in 1.9 seconds.

## 2026-07-15: First-Fit Allocator Model

`Project.Runtime.FreeList` models the state consumed by the shared `rcAllocPayload` instruction builder.  `takeFirstFit` selects the first node with adequate capacity and proves the selected capacity, membership, and one-node length change.  `FreeListAt` records each node's zero refcount, capacity, next link, memory bounds, and separation from its tail, while its frame theorem preserves those facts across unrelated writes.

The compiler already emits every inline allocation through the single `LeanExe.Wasm.Binary.rcAllocPayload` builder.  A compiler change to call the exported allocator would change completed artifacts without eliminating source duplication.  The matching proof will instead verify the current first-fit and bump paths against `FreeListAt`, then reuse that semantic result at its four generated array-allocation sites.

The free-list model passes a warning-failing constrained build in 1.7 seconds.  It introduces no axiom, tactic, or dependency and contains no artifact-specific local indices.  The next theorem must connect one generated allocation walk to `takeFirstFit` before the matching branch proof depends on this model.

`takeFirstFitFrom` retains the predecessor pointer, selected node, successor pointer, and remaining list needed to describe the generated unlink writes.  Its projection equals `takeFirstFit`, so capacity, membership, and one-node length results remain properties of one selection model.  `FreeListAt` now proves that every represented root is nonzero and that separated node regions give duplicate-free roots, which permits a linked-list traversal measure based on the current node's position rather than its address.

`Project.ClobMatchFuel.BookAllocSearch.bookAllocSearchProg_no_fit` proves the full generated book-allocation search when no represented node has enough capacity.  The invariant splits the original free list into a visited prefix and represented suffix, and `scanRemaining_suffix` identifies the loop measure with the suffix length at each cursor.  The theorem preserves the store, returns the zero cursor required by the bump path, and passes a warning-failing constrained build in 3.6 seconds.

An aggregate `Project.ClobMatchFuel.Spec` import check spent most of its two-minute limit rebuilding the unchanged `Helpers` target, completed that dependency, and reached the timeout while rebuilding `FindBest` without a Lean diagnostic.  The unchanged aggregate target will not run again until its remaining dependency objects are current or a substantive proof change reduces that boundary.  The new search target and its modified shared free-list dependency both pass their focused warning-failing builds.

`takeFirstFitFrom_some_decompose` gives the exact successful-selection split into skipped nodes, the selected node, and its successor tail.  It identifies the predecessor pointer through `previousRoot`, identifies the successor and remaining list, and proves that every skipped node was too small.  The shared free-list target passes a warning-failing constrained build in 1.7 seconds with this result.

## 2026-07-15: First-Fit Unlink Semantics

`FreeNode.read64_write64_disjoint` reduces header read-over-write obligations to represented region separation, and `FreeListAt.frame_write64_disjoint` applies that result to a complete retained free list.  `FreeListAt.unlink_takeFirstFitFrom` now proves the exact successful first-fit deletion: a head selection leaves the successor list unchanged, while a later selection writes the selected successor to the predecessor's next field.  `FreeListAt.takeFirstFitFrom_node_disjoint` proves that subsequent initialization writes inside the selected node preserve every retained free-list node.

The proof identifies a nonempty skipped prefix through `List.dropLast_append_getLast`, then applies one adjacent-node unlink theorem.  This structure avoids assumptions about pointer order and uses only the region separation stored by `FreeListAt`.  The warning-failing constrained `Project.Runtime.FreeList` build completes in 2.3 seconds.

## 2026-07-15: Successful Book Allocation Search

`Project.ClobMatchFuel.BookAllocFit.bookAllocSearchProg_fit` proves the exact generated first-fit traversal for every successful `takeFirstFitFrom` result.  A search-state invariant divides the too-small prefix into visited and remaining nodes, while a completed state records the selected root and the post-allocation store.  The measure uses `scanRemaining` until local 81 receives the nonzero selected root, then permits the generated re-entry to exit through its result check.

The head case updates global 1 to the selected successor, while the non-head case writes that successor to the predecessor's next field.  Both cases write the six generated kind-2 fixed-array header words and expose the exact final locals through a continuation-parametric theorem.  `freeListAt_bookAllocFitMem` composes the shared unlink and disjoint-write frame theorems to preserve `FreeListAt` for every remaining node, and the warning-failing constrained module build completes in 7.8 seconds.

The changed `Project.ClobMatchFuel.Spec` import target reached its three-minute constrained timeout without output or a Lean diagnostic.  The focused `BookAllocFit` target had already passed, and no Lean or Lake process remained after the timeout.  The aggregate target will not run again until another source change or a smaller verified boundary reduces its elaboration work.

## 2026-07-15: Fixed-Array Header Boundary

`Project.Clob.fixedArrayHeaderMem` names the six metadata writes that generated fixed-array allocations perform before writing the array length.  `fixedArrayMem` now composes that header transformation with its existing length write, preserving its seven-write behavior.  `fixedArrayHeaderMem_spec` proves the resulting `FreshFixedArrayAt` predicate and gives the book-allocation bump branch a semantic boundary that the later trade allocation can reuse.

The warning-failing constrained `Project.FixedArrayAllocation` build completes in 2.3 seconds.  The helper adds no dependency, axiom, or tactic.  Its proof uses the existing `read_frames` tactic after normalizing the six header addresses.

## 2026-07-15: Book Allocation Bump Path

`Project.ClobMatchFuel.BookAllocBump.bookAllocBumpProg_spec` proves the generated no-result allocation branch from its local-81 test through the heap-top update and six header stores.  Its assumptions state the generated eight-byte minimum capacity, exact nonwrapping top arithmetic, sufficient existing pages, the Wasm page limit, and global 0.  The postcondition records `fixedArrayHeaderMem`, the new global 0 value, the payload root, the computed page count, and the overwritten local frame.

`bookAllocNoFitProg_spec` composes that result with `bookAllocSearchProg_no_fit`, retaining the final predecessor as an irrelevant quantified local.  `freshOrderArrayAt_bookAllocBumpStore` proves the fresh kind-2 header, while `freeListAt_bookAllocBumpStore` preserves represented free nodes whose allocated regions end at or below the old heap top.  The warning-failing constrained `Project.ClobMatchFuel.BookAllocBump` build completes in 6.4 seconds, and the unchanged aggregate target was not retried after its recorded timeout.
