# `leanexegen` Headless Codex Orchestrator

`tools/leanexegen` turns a prose request into a Lean program, a compiled WASM file, and a proof about the exact WASM bytes.  The repository owns the orchestration and invokes the installed Codex CLI in its stable noninteractive mode.  Generation requires working Codex authentication, while verification requires neither Codex nor the LeanExe compiler.

The proof boundary starts from the compiled WASM bytes.  The Talos emitter constructs an untrusted execution-model cache from rendered WAT, while deterministic Lean modules independently decode, validate, and translate the embedded bytes before proving equality to that cache.  The final theorem applies the generated formal specification directly to the validated translation, and its dependency closure contains no generated Source module.

## Command and stages

The generation command accepts one request file and derives the sidecar name from the output name.  `-s` suppresses all standard output, including progress headings, sample results, the final invocation, and verification success; errors and warnings remain on standard error.  Existing output or sidecar paths cause stage seven to fail instead of replacing either path.

```sh
tools/leanexegen -o myprogram.wasm myprogram.txt
```

| Status | Stage | Checked operation |
|--------|-------|-------------------|
| 1 | Job setup | Read the request, locate Codex, record its version, and derive deterministic module names from the request digest. |
| 2 | Formal specification | Ask a fresh Codex task for `expected`, append the fixed `ArtifactSpec`, and check both exact declarations and types with Lean. |
| 3 | Lean program | Give a fresh Codex task the request and frozen formal specification, then type-check, report, and scratch-compile each `Source.compute` candidate. |
| 4 | WASM compilation | Compile the accepted `compute` again, retain the exact bytes, check `wasm-tools`, render WAT, and remove the program task workspace. |
| 5 | Direct artifact proof | Generate deterministic artifact support, give a fresh Codex task the frozen specification and artifact model without Source, and check the artifact theorem. |
| 6 | Sample execution | Run every declared unsigned-scalar sample with pinned Wasmtime and compare stdout with the generated expected result. |
| 7 | Publication | Construct the content-hashed sidecar and install the sidecar and WASM through destination-local renames. |

Usage errors return 64, and unexpected orchestrator defects return 70.  A stage error prints one message to standard error in the form `leanexegen: stage N (name): detail`.  A Codex `questions` or `problems` outcome stops at its task's stage because this version has no interactive question loop.

The publication operation prepares the complete sidecar directory and WASM file before either destination becomes visible.  Each destination rename is atomic, and a caught publication failure removes both newly installed outputs.  POSIX filesystems do not provide one atomic rename for two sibling paths, so a process or machine failure between the two renames can leave the sidecar without the requested sibling WASM file; the sidecar retains its own verified `program.wasm` copy.

## Headless Codex tasks

Every attempt starts a new ephemeral `codex exec` session in a new temporary directory.  The invocation uses `-C`, `--sandbox workspace-write`, `--skip-git-repo-check`, `--ephemeral`, `--json`, `--output-schema`, and `-o`, with the prompt supplied on standard input.  Codex may inspect the provided context with read-only commands but may not edit files or run Lean, Lake, or the compiler; the orchestrator accepts only a schema-validated `generated`, `questions`, or `problems` object.

Each task receives at most five attempts.  The outer process materializes a candidate, runs every Lean, Lake, and compiler diagnostic through `tools/leanrun`, and includes a rejected candidate and its diagnostic in a new Codex task.  Codex receives no persistent conversation or writable repository checkout between attempts.

| Task | Inputs visible to Codex | Required generated source |
|------|-------------------------|---------------------------|
| Formal specification | Request | A complete `FormalSpec` module defining `expected : UInt64 → UInt64`; the orchestrator appends `ArtifactSpec`. |
| Lean program | Request and frozen `FormalSpec` | A complete `Source` module defining `compute : UInt64 → UInt64`, plus unsigned-decimal samples. |
| Artifact proof | Request, frozen `FormalSpec`, generated Talos `Program`, and deterministic artifact-support modules | A complete `Behavior` module proving `artifact_behavior`; Source and the compiler are absent. |

The program task uses the formal file as specification context but does not import it into Source.  After compilation, the orchestrator copies the WASM and WAT into a frozen-artifact directory and removes the complete program workspace and every program-task outcome.  The artifact-proof task therefore receives no source file, source build object, or compiler output other than the frozen artifact model.

## Fixed unary interface

The initial interface accepts and returns one `UInt64`, and the compiled export is `compute`.  The formal Codex task defines `${namespace}.FormalSpec.expected : UInt64 → UInt64`; the orchestrator then appends the following fixed declaration.  A generated Lean check module names and checks both declarations before the formal source can freeze.

```lean
def ArtifactSpec (module_ : Wasm.Module) : Prop :=
  ∃ entry, module_.findExport "compute" = some entry ∧
    ∀ (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit) (n : UInt64),
      Wasm.TerminatesWith env module_ entry initial [.i64 n]
        (fun _ results => results = [.i64 (expected n)])
```

The proof task must prove `${namespace}.Behavior.artifact_behavior : ${namespace}.FormalSpec.ArtifactSpec ${namespace}.module`.  Deterministic `ArtifactResult` source applies `artifact_correct_of` to that exact formal declaration and behavior theorem.  Neither a source theorem nor a compiler-lowering certificate participates in the resulting artifact theorem.

## Proof package and independent verification

A successful command publishes `myprogram.wasm` and `myprogram.proof/`.  The sidecar contains its own `program.wasm`, the request, all three generated sources, deterministic artifact support, samples, host assumptions, tool pins, task reports, and a content index.  The generated Source appears for inspection and provenance, while the verification command builds only the formal specification, Talos program, artifact modules, behavioral proof, embedded-byte checker, and declaration audit.

| Path | Contents |
|------|----------|
| `package.json` | Request identity, fixed formal interface, artifact declarations, warnings, verification command, and hashes for every other file. |
| `artifact.json` | WASM SHA-256 and length, export, invocation shape, fixed property, behavior theorem, and final artifact theorem. |
| `program.wasm` | The exact bytes embedded and proved by the generated Lean modules. |
| `request.txt` | The original prose request, including its original whitespace. |
| `interpretation.json` | The accepted summary and decisions from each of the three Codex tasks. |
| `stage-reports.json` | Codex version, attempt bound, source hashes, accepted and rejected diagnostics, and a hash of each task report. |
| `samples.json` | Arguments, observed outputs, and the Wasmtime argument arrays used during generation. |
| `tool-pins.json` | Lean, Talos, proof-workspace, verifier-source, Node, `wasm-tools`, Wasmtime, and kernel-review identities. |
| `host-assumptions.json` | Host calls, store conditions, ABI expectations, or other assumptions recorded by the formal task. |
| `proof/LeanExeGen/...` | Formal specification, Source, Talos program, Behavior, deterministic artifact proof modules, byte checker, and axiom audit. |

Verification validates the complete file set and every digest, recomputes every task-report and accepted-source hash, checks dependency pins, and checks the fixed formal declaration identity.  It creates a fresh formal declaration checker, byte-comparison module, and declaration-audit module before rebuilding the exact artifact theorem.  It also checks every Git package's recorded revision and tracked-clean state, checks the Lean binary's version and commit, and repeats the configured forbidden-identifier screen over every packaged Lean source.

```sh
tools/leanexegen verify myprogram.proof
```

Transient proof packages depend on the pinned repository package at `proofs/talos/lean`.  They set Lake 4.31.0's root-workspace `packagesDir` layout option to that proof workspace's existing `.lake/packages`, which reuses the pinned dependency checkouts.  A diagnostic transient package used this directory and completed a 3,014-job build through `tools/leanrun`; an earlier incomplete clone without the setting consumed 5.5 GB before removal.

## Acceptance evidence

On 2026-08-03, a live headless run processed the request, “Input and output are UInt64.  Return the input unchanged for every input.”  Codex produced a formal identity specification and Lean identity program that passed their first outer diagnostics.  The artifact-proof task used the first Lean rejection to correct the unfolding order, and its second candidate passed the behavioral and exact-artifact theorems.

The seven stages published a 1,042-byte WASM file with SHA-256 `5561719e6bd6b2b56f2ca932ae16a5f6f518b615053bb766d8e473c4add0a725`.  Wasmtime returned `42` for input `42`.  A separate `tools/leanexegen verify` invocation accepted the sidecar and rebuilt `LeanExeGen.GeneratedRd3267f0041708ae6.Artifact.artifact_correct` without Codex or the compiler.

## Trust boundary and limitations

The final theorem states the fixed formal property of the validated Talos translation of one embedded WASM byte sequence.  The sidecar binds that sequence to SHA-256, byte length, theorem names, task-source hashes, task reports, Lean 4.31.0, the Talos revision, the proof-workspace manifest, and the verifier-source digest.  The declaration audit rejects `sorryAx` and axioms outside the artifact gate's configured allowance.

Every successful generation prints four warnings: Codex interpreted the prose, no theorem connects Source to the formal specification, the theorem covers one exact digest under pinned semantics, and Codex generation and compilation remain outside the artifact proof.  These warnings also appear in `package.json`.  `-s` suppresses standard output but does not suppress warnings on standard error.

The current interface handles one unsigned 64-bit input and output.  Structured ABIs, multiple exports, interactive question resolution, and source certificates remain future work.  Generation can stop on Codex authentication, network, schema, attempt-limit, compiler-acceptance, or proof failures; independent verification of an existing sidecar has no Codex or compiler dependency.
