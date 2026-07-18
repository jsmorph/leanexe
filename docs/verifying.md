# Verifying a Program

LeanExe uses two tools for Talos proofs.  The artifact tool compiles one registered Lean entry and generates the Talos model of its current WASM output.  The proof tool repeats that generation before asking Lean to check the handwritten specification, so a successful proof always concerns output from the current source and compiler.

The compiler remains outside the proof's trusted base.  The Lean kernel checks the theorem over Talos's WASM model, and the Talos decoder constructs that model from WAT rendered from the generated WASM.  A distributed artifact must come from the same source, compiler, and pinned artifact tools used by the gate, or its bytes must be compared with the gate's ignored `program.wasm` output.

## Inputs and Outputs

| Stage | Explicit inputs | Other inputs used by the stage | Outputs | Human work |
|-------|-----------------|--------------------------------|---------|------------|
| Write and test the program | A Lean source module and exported entry definition. | The accepted source subset, public ABI, compiler semantics, and ordinary test infrastructure. | Tracked Lean source and tests; checked declarations under the ignored root `.lake` tree. | Choose the computation, types, error behavior, and test cases. |
| `talos-artifact.js prepare` | A case name and its entry in `proofs/talos/cases.json`. | Lean 4.31.0, the root Lake project, `lean-wasm`, `wasm-tools` 1.251.0, the pinned Talos revision, and the required systemd resource policy. | Ignored WASM and WAT under `proofs/talos/.generated/<case>/`; an ignored `lean/Project/<Case>/Program.lean`. | Inspect the generated instruction stream and decide what property warrants proof. |
| Develop the specification | The source meaning, generated `Program.lean`, generated WAT, and the intended claim. | Talos semantics, the shared runtime theorems, representation predicates, arithmetic lemmas, and examples from completed cases. | Tracked `Spec.lean` and any tracked helper proof modules under `lean/Project/<Case>/`. | State adequate preconditions and postconditions, then construct the proof. |
| `talos-proof.js check` | A case name or `--all`, the registry, current source, and handwritten proof modules. | Every artifact-stage dependency, the proof Lake project, its pinned manifest, runtime pins, and aggregate imports. | Ignored generated files and Lake outputs; a zero exit status only after the selected theorem builds. | Interpret a failure and change source, specification, or proof according to its cause. |

The artifact stage creates Talos's required `rust/<case>/Cargo.toml` and `rust/build/<case>/` layout inside an operating-system temporary directory.  It deletes that directory after Talos emits `Program.lean`, and cleanup failures make the command fail.  The repository therefore contains no tracked Rust crate, Cargo workspace, WASM, WAT, or generated Lean model.

The persistent case consists of the source program, its tests, one registry entry, runtime pins, an aggregate import after completion, and handwritten proof modules.  A case may divide its proof among many files, with `Spec.lean` importing the final theorem.  The ignored `Program.lean` remains a local dependency that either tool can regenerate.

## Resource Policy

Both tools enforce the repository's cgroup policy for every Lake, Lean, `lean-wasm`, and Talos verifier process.  Each child receives `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and a stage-specific timeout.  The tools run stages serially and stop when systemd cannot create the required user scope.

Do not wrap these two commands in a second `systemd-run` scope.  The tools create a separate limited scope for each expensive child, and an outer scope complicates diagnostics without strengthening the limits.  Do not run either tool while another Lean or Lake process is active.

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

The proof normally enters through `TerminatesWith.of_wp_entry_for`, changes to a `wp` goal over the generated function body, and composes bounded instruction regions.  [`Project/Common.lean`](../proofs/talos/lean/Project/Common.lean) supplies address and read-over-write tools, while [`Project/Runtime`](../proofs/talos/lean/Project/Runtime) supplies generic allocator, retain, release, free-list, and recursive teardown results.  [Proof Engineering Plan Notes](plan-notes.md) records reusable CLOB representations, allocation theorems, copy invariants, and elaboration boundaries.

Divide a generated function at calls, loops, branches, allocations, copy loops, final stores, and result construction.  Give each region an explicit instruction list or a small definitionally equal extraction, and state its semantic postcondition before proving the generated adapter.  A target that reaches its timeout without a diagnostic requires a smaller theorem or a reusable semantic lemma before another build.

## Proof Tool

The focused gate regenerates the artifact and model before building the registered specification target.  It reports Lean warnings but fails on compilation, model generation, runtime-pin, or proof errors.  An incomplete case can use the same command, although its successful build does not count it among the completed proofs.

```sh
tools/talos-proof.js check fold_sum
```

After the theorem is complete, set `complete` to `true` and import `Project.<Case>.Spec` from [`Project.lean`](../proofs/talos/lean/Project.lean).  The aggregate gate verifies that completed registry entries match the specification imports and that every registered case appears in the runtime checks.  It then regenerates all registered cases serially and builds the complete `Project` target.

```sh
tools/talos-proof.js check --all
```

The final gate can fail because the source no longer compiles, `wasm-tools` has the wrong version, Talos rejects the WAT, the generated model does not compile, a runtime definition changed, a handwritten theorem no longer matches the current instruction stream, or the registry and aggregate imports disagree.  It also fails when a child exceeds its timeout, the cgroup manager rejects a required limit, a generated output cannot be replaced, or a temporary directory cannot be removed.  These failures preserve the stage name and child exit status so the next investigation starts at the first failed boundary.

## Committed Files

Commit the source module, tests, `cases.json`, runtime pins, `Project.lean` import after completion, `Spec.lean`, and every handwritten helper it imports.  Commit documentation that states the theorem's scope and any new reusable proof result.  `git status --ignored` may show local generated output, but ordinary `git status` must omit `.generated` artifacts and every `Project/<Case>/Program.lean`.

Never edit `Program.lean`, and never recreate a persistent `proofs/talos/rust` tree.  Run the artifact tool again when the model needs to change, then repair the handwritten theorem against the new instruction stream.  Record focused and aggregate gate results in `devnotes.md` without treating an old cached build as current evidence.
