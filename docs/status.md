# Development Status

This report records the repository state on 2026-08-03.  The source-driven Talos proof set covers all twenty registered artifacts, while the artifact verifier checks their exact binary WebAssembly files through decoding, validation, Talos translation, and behavior.  The [development plan](../plan.md), [artifact-verification plan](../plans/artifact-verification.md), and [development journal](../devnotes.md) record the remaining work and the evidence for completed checks.

## Summary

LeanExe has completed the runtime-ownership, single-evaluation, and CLOB proof phases of the source-driven plan.  Input-generic Talos proofs cover `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth`, in addition to the earlier artifacts.  `ClobDepth.Func7.func7_terminates` proves that the exported depth function terminates for every represented order book under the stated allocator budget and returns two owned level arrays representing the exact source `depthL` bids and asks.

The artifact verifier has a faithful raw syntax, bounded binary parser, LEB128 and primitive decoders, a restricted Core 3.0 module decoder, a profile validator, and translation to the Talos module representation.  Theorems prove decoder soundness against the independent binary grammar and validator soundness against the independent `CoreValid` judgment.  All twenty registered binaries now have frozen packages, exact embedded bytes, checked translations to their Talos execution models, and artifact-level correctness theorems that reuse their existing behavioral specifications.

## Artifact Verifier

The accepted profile covers the type, function, memory, global, export, and code sections and the instruction forms emitted by the current compiler.  The decoder rejects unsupported sections and opcodes, enforces section order and sizes, parses structured control, and requires complete input consumption.  The validator checks the profile's indices, types, stack effects, branches, mutability, memory operations, exports, and function-body agreement before translation.

`Wasm.Binary.Grammar.Encodes` gives an independent declarative grammar for the accepted bytes.  `Wasm.Binary.Proof.decode_sound` proves that every successful complete-file decode satisfies that grammar, including section order and the absence of unparsed profile fields.  `Wasm.Binary.Proof.validate_sound` proves that every successful validator result satisfies `CoreValid`, covering the accepted instruction stack effects, indices, globals, exports, memory, and function/code agreement.

Each artifact target proves successful decoding and validation of its embedded bytes.  Generated raw-module caches avoid repeated whole-file reduction, while checked decode equalities and translation equalities prevent another cache from entering the proof.  Each closed `artifact_module_eq_cache` theorem identifies the validated artifact's Talos module with the execution module named by the registered behavioral theorem.

| Boundary | Current evidence | Formal status |
|----------|------------------|---------------|
| Exact bytes | Twenty content-addressed packages contain `program.wasm` and strict manifests; Lean modules embed every byte. | The aggregate gate checks file digest, length, package equality, and embedded-byte equality. |
| Binary decoding | Primitive and corruption tests pass; all twenty current binaries decode. | `decode_sound` connects successful decoding to the declarative grammar. |
| Validation | Repository fixtures reject, fifteen pinned official invalid modules match exact decoder or validator errors, and all twenty artifact modules validate. | `CoreValid` is independent of the executable validator, and `validate_sound` builds without warnings. |
| Talos translation | All twenty translations match their cached execution models. | Per-function and module cache-equality theorems pass for all twenty packages. |
| Behavior | Every manifest records the concrete source behavior theorem for the cached execution module, and the closed artifact theorem proves equality with that module. | Schema-three `check-all` passed all twenty behavioral specifications and exact declaration checks on 2026-08-03. |
| Artifact command | `tools/artifact-proof.js` checks one registered package or all packages without LeanExe or `wasm-tools`. | Every Lean child runs through the shared, resource-limited `tools/leanrun` path, and driver signals reach the active child process group. |
| Trusted kernel | Both workspaces pin Lean 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`. | Lean 4.31.0 accepts the archived reproduction; the owner accepts the defect after the exact local lexical audit recorded by the release evidence. |

## Current State

| Item | State | Evidence |
|------|-------|----------|
| Depth artifact | Complete | `cases.json` carries `complete: true`; `tools/talos-proof.js check clob_depth` passed on 2026-07-18. |
| Aggregate imports | Current | `Project.lean` imports `Project.ClobDepth.Spec`. |
| PostOnly repairs | Complete | Focused warning-failing builds pass in 12 and 7.1 seconds. |
| Artifact executable path | Twenty artifacts pass | Identity, embedded-byte, decode, validation, translation, and generated-cache comparison checks pass under the constrained runner. |
| Artifact formal path | Twenty artifacts pass | Decoder and validator soundness plus every exact translation and artifact-correctness target build. |
| Behavioral aggregate | Twenty artifacts pass | `tools/artifact-proof.js check-all` passed every specification and the manifest theorem check on 2026-08-03. |
| Repository execution | Complete gate passes | `node test/run_all.js` passed 791 accepted cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases on 2026-08-03. |
| Semantic conformance | Twenty-five selected official files pass with one known upstream warning | Talos produced 3,853 passes, six configured assertion failures, and 627 skips; Wasmtime passed every selected file. |
| Decoder and validator conformance | Fifteen official invalid modules match | Each pinned file, assertion kind, line, classification stage, and error constructor matched on 2026-08-03. |
| Lean toolchain | Lean 4.31.0 pinned in both workspaces | The selected release accepts the archived reproduction; the local audit covers literal `addDecl` and `inductDecl` references in the artifact proof tree and its two local `LeanExe` imports. |
| Release evidence | Draft with matching warm gate receipts | The immutable source revision and matching cold-checkout receipt remain unavailable until this implementation is committed. |

## Depth Proof Structure

The proof divides generated function 3 at the scan, branch, allocation, copy, store, and result boundaries, with each region's theorem passing an exact local frame to the next.  The missing-price branch appends one level through bump allocation and a stride-two copy, while the found-price branch allocates a same-length array, copies every level word, and replaces the matched quantity with modular addition.  Both branches share the empty free-list search theorem, the generic bump theorem, the level-copy invariant, and the fixed-array allocation library, and `Func3.UpdateResult` states their one conclusion: the returned array represents `addLevelL levels price qty` with a capacity derived from the result length.

Function 6 reads the order count, allocates two empty level arrays through one shared adapter, and folds the orders on the selected side.  `Func6Fold` defines the represented levels, match count, heap top, result root, owner, and capacity after any order prefix, and bounds the heap top by `g0 + 112 + k * stepBytes count`.  `Func6Loop` carries the loop invariant with exact allocator globals, the owned result array, the preserved orders representation, and the byte frame below the initial heap top; its body theorem steps each order through `wp_call_tw` and the function 3 `TerminatesWith` wrapper, and one budget premise discharges every per-call fit.

Function 7 composes the two side folds.  The second fold runs at the first fold's exact heap top and counters, the first result array survives through the below-heap byte frame, and `Func7.Result` states ownership of both arrays with `depthSideL` contents, the preserved input orders array, the exact three allocator globals, page equality, and bytes below the initial heap top.  `Project.ClobDepth.Spec` restates the returned contents through `Model.depthL` and exposes exact modular per-price aggregation with its bounded natural-number interpretation.

## Verification Status and Risks

Every depth module builds through the required constrained scope with `--wfail`.  The largest focused builds are the loop body at 10 seconds and the empty-allocation adapter at 9.1 seconds; every other depth module builds in under seven seconds.  The source-driven focused gate still tests regeneration, while the separate frozen package now establishes exact-byte identity, decoding, validation, translation equality, and the depth specification without invoking the compiler.

Folded-frame lemmas, `wp_run_folded`, reusable block and loop scaffolds, and smaller module boundaries closed the earlier `Validate`, `PushTwice`, `SharedPair`, and `PairFree` elaboration failures.  The LEB128 proof now composes reusable positive and negative allocation, iteration, completion, and prefix lemmas; its complete specification passed before the gate continued through all eight CLOB artifacts.  The largest observed modules in the successful aggregate were `Project.ClobCancel.Spec` at 1,092 seconds and `Project.ClobMatchFuel.FindBest` at 696 seconds, both within the standard limits.

The source-driven proof gate regenerates all twenty models before building `Project`, while the artifact gate starts from frozen bytes and does not read source or invoke the compiler.  Both tools route every Lean-based child through the repository runner, but they establish different facts: compiler-workflow consistency versus correctness of an identified binary.  The development journal records current aggregate, execution, decoder, validator, and translation results with their limitations.

## Required Lean and Lake Resource Policy

Every direct `lean`, `lake`, Lean compiler, or `lean-wasm` command must run through `tools/leanrun`.  Repository Node drivers and verification tools route their Lean-based children through that runner.  The runner shares `/tmp/vq-leanrun.<uid>/1` with `../vq/tools/leanrun`, preventing concurrent Lean jobs from separate terminals in either repository for the same user.

```sh
tools/leanrun --timeout <duration> <lean-or-lake-command>
```

`MemoryHigh=4G` begins memory-pressure handling at four gibibytes, `MemoryMax=6G` enforces the hard limit, `MemorySwapMax=1G` bounds swap growth, and `CPUQuota=100%` limits the scope to one core in aggregate.  The runner sets `LEAN_NUM_THREADS=1`, `nice -n 10`, and `ionice -c 3`, then applies the requested execution timeout after it acquires the lock.  A timeout without a diagnostic requires proof or module division before another attempt.

The focused proof command starts from `proofs/talos/lean` because its `lakefile.toml` owns the Talos project.  Repository-level scripts start from the repository root, while the Talos and artifact entry points call the runner for each child.  Signal-aware process-group execution ensures that interrupting a Node driver terminates its active runner and descendants.

```sh
cd /media/hd2/src/leanexe
tools/talos-proof.js check clob_depth
tools/talos-proof.js check --all
```

Do not substitute `ulimit -v`, `prlimit --as`, a background process, or an unbounded bare `lake build` for this policy.  Do not wrap the runner or repository drivers in a second resource scope.  If the runner cannot acquire its lock or create the required user scope, stop rather than running Lean without the enforced boundary.

## Next Order of Work

The official-corpus gate now pins CodeLib, the WebAssembly testsuite, `wasm-tools`, and Wasmtime, then runs twenty-five exact `.wast` files through Talos and Wasmtime.  Talos reports 3,853 passes, six configured assertion failures, and 627 skips without cascades, decoder errors, interpreter errors, or fuel exhaustion, while Wasmtime passes every selected file.  The gate accepts the exact imported-memory discrepancy as an upstream warning, removes the warning when it disappears, and rejects every changed or additional failure; the [Talos imported-memory defect report](telos-bug.md) records its provenance and scope.

The selected corpus now covers the accepted integer, control, call, local, memory, conversion, and expression forms, with `global.wast` recorded as a profile-coverage gap because that file mixes local globals with imported globals and a table form.  Fifteen separately pinned official invalid modules reach the artifact decoder or validator and match exact error constructors.  The draft release record binds all artifact identities, theorem names, pins, input digests, and observed results; completion requires an immutable revision and its matching cold-checkout receipt.
