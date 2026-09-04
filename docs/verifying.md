# Verifying a Program

LeanExe uses five tools for source-driven proof, exact-artifact proof, empirical semantic comparison, and release evidence.  The source artifact tool compiles one registered Lean entry and generates the Talos model of its current WASM output, while the source proof tool repeats that generation before checking the handwritten specification.  The exact-artifact tool starts from a frozen binary package, the conformance tool runs a pinned official WebAssembly corpus slice through Talos and Wasmtime, and the release tool binds their results to one repository identity.

The compiler remains outside both proofs' trusted base.  The source-driven gate checks the Talos model decoded from generated WAT, while the exact-artifact theorem checks the Talos translation of a validated module decoded from embedded binary bytes.  A distributed binary receives the artifact theorem only when its complete byte sequence equals the frozen package and Lean's embedded value.

## Inputs and Outputs

| Stage | Explicit inputs | Other inputs used by the stage | Outputs | Human work |
|-------|-----------------|--------------------------------|---------|------------|
| Write and test the program | A Lean source module and exported entry definition. | The accepted source subset, public ABI, compiler semantics, and ordinary test infrastructure. | Tracked Lean source and tests; checked declarations under the ignored root `.lake` tree. | Choose the computation, types, error behavior, and test cases. |
| `talos-artifact.js prepare` | A case name and its entry in `proofs/talos/cases.json`. | The root compiler's pinned Lean version, the proof workspace's separately pinned Lean version, `lean-wasm`, `wasm-tools` 1.251.0, the pinned Talos revision, and either the standard systemd resource policy or explicitly authorized local runner mode. | Ignored WASM and WAT under `proofs/talos/.generated/<case>/`; a tracked `lean/Project/<Case>/Program.lean` proof cache. | Inspect any changed instruction stream and decide what property warrants proof. |
| Develop the specification | The source meaning, generated `Program.lean`, generated WAT, and the intended claim. | Talos semantics, the shared runtime theorems, representation predicates, arithmetic lemmas, and examples from completed cases. | Tracked `Spec.lean` and any tracked helper proof modules under `lean/Project/<Case>/`. | State adequate preconditions and postconditions, then construct the proof. |
| `talos-proof.js check` | A case name or `--all`, the registry, current source, and handwritten proof modules. | Every artifact-stage dependency, the proof Lake project, its pinned manifest, runtime pins, and aggregate imports. | Ignored generated files and Lake outputs; a zero exit status only after the selected theorem builds. | Interpret a failure and change source, specification, or proof according to its cause. |
| `artifact-proof.js check` | An exact `program.wasm` path and registered artifact proof target. | The content-addressed package, strict manifest and registry, embedded bytes, binary verifier, Talos semantics, and behavioral proof modules. | Lake outputs; a zero exit status only after identity, formal artifact, behavior, and manifest-declaration checks pass. | Review the manifest, trusted revisions, host assumptions, and behavioral statement. |
| `artifact-conformance.js check` | The pinned conformance configuration and exact official `.wast` files and command lines. | Pinned CodeLib and testsuite revisions, `wasm-tools` 1.251.0, Talos, and Wasmtime 44.0.0 with the recorded feature settings. | Exact decoder or validator classifications, per-file Talos counts, and Wasmtime outcomes; a zero exit status only when every configured result matches. | Review invalid-module classifications, coverage labels, skipped command kinds, and every semantic discrepancy. |

The source artifact stage creates Talos's required `rust/<case>/Cargo.toml` and `rust/build/<case>/` layout below the repository's ignored `tmp/` directory.  It deletes that directory after Talos emits `Program.lean`, and cleanup failures make the command fail.  The source-driven tree retains no generated WASM or WAT, while it tracks each generated Lean model as an untrusted proof cache required by artifact-only and cold-checkout verification.

The persistent source-driven case consists of the source program, its tests, one registry entry, runtime pins, an aggregate import after completion, the generated `Program.lean` cache, and handwritten proof modules.  A case may divide its proof among many files, with `Spec.lean` importing the final theorem.  Either source-driven tool can regenerate the cache, and a byte change marks a changed proof subject that must pass the exact-artifact equality and behavioral gates.

## Resource Policy

All four tools call `tools/leanrun` for every Lake, Lean, `lean-wasm`, and Talos verifier process.  In standard mode each child receives `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, `LEAN_NUM_THREADS=1`, and a stage-specific timeout.  The runner shares the same-user `../vq` lock, and the tools stop when they cannot acquire that lock or create the required user scope.

In a container without a systemd user scope, an explicit user-authorized
`LEANRUN_LOCAL=1` on one of these tools keeps every child local and retains the
pinned toolchain, shared lock, stage timeout, `LEAN_NUM_THREADS=1`, `nice`, and
`ionice`.  The runner warns that the cgroup CPU, memory, and swap limits are
not enforced.  The mode is never an automatic fallback.  Invoke the tool
directly with the variable; do not wrap a runner-calling tool in
`tools/leanrun`, because its child runners must acquire the lock themselves.

Do not wrap these commands in a second resource scope.  The tools create a separate limited scope for each expensive child, and the shared lock queues behind any participating Lean or Lake process.  The Node drivers use signal-aware process groups, so `SIGINT` or `SIGTERM` reaches the active runner, timeout process, Lake process, and Lean child before the driver exits.

## Artifact Tool

Register the source module and entry in [`proofs/talos/cases.json`](../proofs/talos/cases.json).  The registry requires a snake-case case name, the checked Lean module, the fully qualified entry, the Pascal-case proof module, the final specification target, and a completion flag.  Set `complete` to `false` until the case has its intended theorem and belongs in the aggregate proof library.

```json
{
  "name": "fold_sum",
  "module": "LeanExe.Examples.ByteArrayPrograms",
  "entry": "LeanExe.Examples.ByteArrayPrograms.foldSum",
  "leanModule": "FoldSum",
  "specTarget": "Project.FoldSum.Spec",
  "complete": true
}
```

Generate one case from the repository root.  The tool validates the `wasm-tools` version, builds the compiler and source module, compiles the entry, renders WAT, invokes Talos through temporary Cargo-shaped input, and replaces local outputs only after every stage succeeds.  Content-identical outputs retain their timestamps, which prevents needless proof rebuilds.

```sh
tools/talos-artifact.js prepare fold_sum
```

The generated files support inspection and proof development.  Read `proofs/talos/.generated/fold_sum/program.wat` when function indices, control flow, or instruction boundaries require examination, and import `Project.FoldSum.Program` from handwritten proof modules.  Regenerate these files after changing the source, compiler, Talos pin, or `wasm-tools` pin.

## Handwritten Proof

Add the generated module import and four runtime equalities to [`Project/Runtime/Checks.lean`](../proofs/talos/lean/Project/Runtime/Checks.lean).  The runtime function indices follow the user functions in the generated module, and release takes its own index because its body calls itself recursively.  A failed `rfl` identifies a generated runtime change that the shared runtime library must address.

```lean
example : Project.FoldSum.func1Def = allocFuncDef := rfl
example : Project.FoldSum.func2Def = resetFuncDef := rfl
example : Project.FoldSum.func3Def = retainFuncDef := rfl
example : Project.FoldSum.func4Def = releaseFuncDef 4 := rfl
```

State the primary theorem over meaningful inputs and relate the WASM result to the source computation.  Include memory layout, address and page bounds, ownership, allocator state, counters, and frame conditions wherever the generated program depends on them.  A fixed example can test the proof machinery but does not establish an input-generic program theorem.

The proof normally enters through `TerminatesWith.of_wp_entry_for`, changes to a `wp` goal over the generated function body, and composes bounded instruction regions.  [`Project/Common.lean`](../proofs/talos/lean/Project/Common.lean) supplies address and read-over-write tools, while [`Project/Runtime`](../proofs/talos/lean/Project/Runtime) supplies generic allocator, retain, release, free-list, and recursive teardown results.  [Artifact Proving](artifact-proving.md) explains the shared ProofKit, annotation, LTG, journal, and independent-checking boundaries, while [Artifact-Proof Strategies](proof-strategies.md) records general construction guidance.

Divide a generated function at calls, loops, branches, allocations, copy loops, final stores, and result construction.  Give each region an explicit instruction list or a small definitionally equal extraction, and state its semantic postcondition before proving the generated adapter.  A target that reaches its timeout without a diagnostic requires a smaller theorem or a reusable semantic lemma before another build.

## Proof Tool

The focused gate regenerates the artifact and model before building the registered specification target.  It reports Lean warnings but fails on compilation, model generation, runtime-pin, or proof errors.  An incomplete case can use the same command, although its successful build does not count it among the completed proofs.

```sh
tools/talos-proof.js check fold_sum
```

After the theorem is complete, set `complete` to `true` and import `Project.<Case>.Spec` from [`Project.lean`](../proofs/talos/lean/Project.lean).  The aggregate gate verifies that completed registry entries match the specification imports and that every registered case appears in the runtime checks.  It then regenerates all registered cases serially and builds the complete `Project` target; the 2026-08-26 run passed all twenty cases.

```sh
tools/talos-proof.js check --all
```

The final gate can fail because the source no longer compiles, `wasm-tools` has the wrong version, Talos rejects the WAT, the generated model differs from the tracked cache, the cached model does not compile, a runtime definition changed, a handwritten theorem no longer matches the current instruction stream, or the registry and aggregate imports disagree.  It also fails when a child exceeds its timeout, the standard-mode cgroup manager rejects a required limit, a generated ignored output cannot be replaced, or a temporary directory cannot be removed.  These failures preserve the stage name and child status so the next investigation starts at the first failed boundary.

## Exact-Artifact Tool

An exact-artifact package has the path `proofs/artifacts/<case>/<sha256>/` and contains `program.wasm` and `manifest.json`.  The separate artifact registry maps its case, digest, manifest, and proof target, while `Project.<Case>.ArtifactBytes` embeds the complete byte sequence in Lean.  Schema three names the embedded bytes, decoded raw module, cached execution module, closed module-equality theorem, and concrete source behavioral theorems, while recording both Lean pins, the Talos revision, the normative verifier-source digest, and host assumptions.

Check an external binary by passing its path and the registered artifact target.  The command rejects an unregistered target, a manifest mismatch, a changed digest or length, any byte difference from the immutable package, or any difference from Lean's embedded byte value.  It then builds the exact artifact theorem and behavioral specification, checks the expected theorem types, and rejects `sorryAx` or an axiom outside the standard logical axioms and generated decision-certificate families recorded by the artifact format.

```sh
tools/artifact-proof.js check \
  proofs/artifacts/fold_sum/b599860eb8fe3937148455c27c8cfca5473f967001e563530b4790c43017e3b5/program.wasm \
  Project.FoldSum.ArtifactTranslation
```

`check-artifacts` performs the identity, embedded-byte, and exact-artifact theorem stages for all twenty packages.  `check-all` adds every behavioral specification and the aggregate manifest-declaration check.  Neither aggregate mode invokes LeanExe, reads a source program, or invokes `wasm-tools`.

## Semantic Conformance Tool

The conformance configuration pins the CodeLib and official WebAssembly testsuite revisions, Wasmtime version and feature options, twenty-five exact execution files with coverage labels, and fifteen invalid-module commands identified by file, assertion kind, and source line.  The command verifies those revisions and executable versions, builds the pinned Talos testsuite executable and the artifact classifier, and runs each operation serially.  A temporary one-file corpus selects each execution filename exactly, avoiding the Talos harness's substring matching.

```sh
tools/artifact-conformance.js check
```

The invalid-module stage extracts each configured official module and requires the exact decoder or validator error constructor recorded in the configuration.  `wasm-tools` adds custom name sections when encoding text-origin `assert_invalid` modules, so the command strips custom sections from those cases before classification.  It preserves raw `assert_malformed` binary modules byte-for-byte, and the 2026-08-26 run matched all fifteen classifications, including truncation, version, section, integer-width, alignment, stack, and memory-limit failures.

Talos executes supported assertions and reports unsupported command kinds as skips, so the invalid-module stage supplies separate evidence for the artifact decoder and validator.  The 2026-08-26 execution run produced 3,853 passes, six known assertion failures, 627 skips, and no cascades, decoder errors, interpreter errors, or fuel exhaustion in Talos, while Wasmtime passed all twenty-five files with `function-references=y`.  The command warns only when the failures exactly match the six imported-memory rows recorded for `memory_grow.wast`; an upstream repair removes the warning, while any changed or additional failure stops the gate.

## Release Evidence Tool

The release file binds the artifact registry hash, every package-manifest hash, exact theorem names, verifier and release-input digests, tool pins, and machine-produced gate receipts.  The release-input digest includes every project proof source, tracked Talos execution cache, recursive local `LeanExe` import, Lake definition, selected binary, manifest, pin, and verification driver used by the two gates.  Its status follows the immutable source revision, accepted kernel disposition, matching aggregate and conformance receipts, and a successful cold-checkout receipt; removing a blocker string without satisfying its corresponding field makes validation fail.

```sh
tools/artifact-release.js inspect
tools/artifact-release.js refresh
tools/artifact-release.js check-ready
tools/artifact-release.js check-cold <revision>
```

`inspect` validates the draft without claiming release readiness, while `refresh` reconstructs package records and consumes matching receipts from `build/evidence`.  `check-ready` returns a failure until every derived condition holds.  `check-cold` compares the current and cloned release inputs before setup, checks the exact Lean and dependency revisions, rejects tracked mutations after setup or either gate, reruns both gates, and writes the cold receipt before removing its temporary checkout.  The current record carries input digest `f57e509b9e4967329d7c0dd63e2f4041926a66877af6b9c98e5c4c99ad562589` at source revision `08bdaa78a3efa2badc5922a0250cc4c9710a8a29`.  Its aggregate proof, semantic-conformance, and cold-checkout receipts are pending because the self-hosted-emitter implementation changed the release inputs; the accepted 2026-08-26 receipts bind only the previous digest.

## Committed Files

Commit the source module, tests, `cases.json`, runtime pins, `Project.lean` import after completion, generated `Program.lean` proof cache, `Spec.lean`, and every handwritten helper it imports.  An exact-artifact migration also commits the content-addressed binary and manifest, artifact registry entry, embedded bytes, decoded caches, and exact translation theorem modules.  A conformance change commits `proofs/talos/conformance.json`, the driver or parser tests it changes, and documentation of the pinned revisions and observed result.  Every proof change also records the theorem's scope, host assumptions, and new reusable results.

Never edit `Program.lean` by hand, and never recreate a persistent `proofs/talos/rust` tree.  Run the artifact tool when the model needs to change, review the tracked cache diff, then repair the handwritten theorem against the new instruction stream.  Record focused and aggregate gate results in `devnotes.md` without treating an old object file as current evidence.
