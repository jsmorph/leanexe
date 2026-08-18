# `leanexegen` Headless Codex Orchestrator

`tools/leanexegen` turns a prose request into a Lean program, a compiled WASM file, and a proof about the exact WASM bytes.  The repository owns the orchestration and invokes the installed Codex CLI in its stable noninteractive mode.  Generation requires working Codex authentication, while verification requires neither Codex nor the LeanExe compiler.

The proof boundary starts from the compiled WASM bytes.  The Talos emitter constructs an untrusted execution-model cache from rendered WAT, while deterministic Lean modules independently decode, validate, and translate the embedded bytes before proving equality to that cache.  The final theorem applies the generated formal specification directly to the validated translation, and its dependency closure contains no generated Source module.

## Command and stages

The generation command accepts one request file and derives the sidecar name from the output name.  `--knowledge` selects a versioned knowledge forest, with `knowledge/forest.json` as the default.  Each progress heading records the stage's UTC start time in ISO 8601 format.  `-s` suppresses all standard output, including progress headings, sample results, the final invocation, and verification success; errors and warnings remain on standard error.  Existing output or sidecar paths cause stage seven to fail instead of replacing either path.

```sh
tools/leanexegen -o myprogram.wasm myprogram.txt
tools/leanexegen --knowledge snapshots/accepted/forest.json \
  -o myprogram.wasm myprogram.txt
```

| Status | Stage | Checked operation |
|--------|-------|-------------------|
| 1 | Job setup | Read the request, locate Codex, record its version, and derive deterministic module names from the request digest. |
| 2 | Formal specification | Ask a fresh Codex task for `expected` and `heapReserveBytes`; the task iterates with Lean, then the outer process appends the fixed `ArtifactSpec` and checks all exact declarations and types. |
| 3 | Lean program | Give a fresh Codex task the request and frozen formal specification; the task iterates through type-check, report, and scratch-compile commands before the outer process repeats them. |
| 4 | WASM compilation and freezing | Compile the accepted `compute` again, retain the exact bytes, check `wasm-tools`, render WAT, and remove the program task workspace. |
| 5 | Direct artifact proof | Generate deterministic artifact support and check any starter predicted complete.  Accept a successful full artifact check directly; otherwise give a fresh Codex task the source-free specification and artifact model, let it iterate with Lean, and repeat the artifact check outside the task. |
| 6 | Sample execution | Allocate each input array through the Wasmtime host runner, invoke `compute`, decode the returned array, and compare every element with the expected output. |
| 7 | Publication | Construct the content-hashed sidecar and install the sidecar and WASM through destination-local renames. |
| 8 | Results | Print the checked sample inputs and outputs, followed by a command that runs the published WASM file. |

Usage errors return 64, and unexpected orchestrator defects return 70.  A generation-stage error prints `leanexegen: stage N (name): detail`, while a learning failure prints `leanexegen: learn <mode>: detail` and returns one.  A Codex `questions` or `problems` outcome stops at its task's stage because this version has no interactive question loop.

The publication operation prepares the complete sidecar directory and WASM file before either destination becomes visible.  Each destination rename is atomic, and a caught publication failure removes both newly installed outputs.  POSIX filesystems do not provide one atomic rename for two sibling paths, so a process or machine failure between the two renames can leave the sidecar without the requested sibling WASM file; the sidecar retains its own verified `program.wasm` copy.

### Controlled reproof

The `reprove` command replaces only the generated `Behavior` module.  It reads a valid proof package and preserves the request, formal specification, Source, WASM bytes, Talos `Program`, deterministic artifact modules, artifact declaration record, formal and program task reports, samples, and host assumptions.  Stage five checks a predicted-complete starter directly or gives Codex the same source-free artifact-proof context with the current proof catalog, while stages two through four require no regeneration.

```sh
tools/leanexegen reprove -o revised.wasm myprogram.proof
```

The command permits `proofKitSourceSha256` to differ between the input package and the current checkout.  Every other tool pin must match, the Codex CLI identity must match the identity recorded by the package, and no frozen module may import the mutable proof-kit module.  Publication validates the new package, compares the output WASM and artifact record with the input, and compares every frozen Lean module byte-for-byte before installing either output.

`--new-codex-series` permits one explicit Codex CLI identity change when starting a new timing series.  The option requires the installed identity to differ from the input package's artifact-proof identity, preserves the formal and program task identities, and records all three task identities separately in stage-report schema two.  Later reproofs from the resulting package use the ordinary command and require the recorded artifact-proof identity again.

```sh
tools/leanexegen reprove --new-codex-series \
  -o revised.wasm myprogram.proof
```

The option changes no frozen source, formal specification, compiler output, decoded program, or tool pin.  Comparisons across the identity boundary remain invalid, so a new series requires both its baseline and experimental variants under the new identity.  Package validation retains the earlier formal and program identities instead of attributing those tasks to the replacement CLI.

### Controlled annotation

The `annotate` command recompiles a frozen package's `Source` with the current compiler, requires byte-for-byte equality with the frozen WASM, validates the complete compiler sidecar against the decoded program, and generates checked region equalities.  `--only-region` then retains one named semantic region, along with every direct-call region required for complete call coverage, and may occur more than once.  An unknown, duplicate, or ambiguous region name fails package creation, while a calls-only baseline can name the required direct-call regions without selecting another semantic region.

```sh
tools/leanexegen annotate \
  --only-region function-0.while-loop-0 \
  -o scalar-only.proof myprogram.proof
```

### Stateful knowledge composition

Leanexegen represents accumulated proof knowledge as files with checked identities.  A completed proof package can yield an experimental knowledge package, which review can promote into a forest snapshot for later selection through `--knowledge`.  Each proof package archives the filtered snapshot used by its proving agent, so the sequence of work remains reproducible.

`record` turns an accepted proof package into an experimental knowledge package containing the accepted proof, journal, annotations, recipes, task features, telemetry, and prior knowledge identity.  Its catalog entry excludes the motivating artifact, so a later measured reproof cannot retrieve its own accepted proof.  The package remains outside every selected forest until promotion.

`propose` gives the same run evidence and archived knowledge snapshot to a separate headless Codex task.  The task writes a learning journal and proposes one guidance entry, worked example, checked lemma, or checked tactic; checked Lean source must pass the prescribed Lean build during the task and an outer build afterward.  The resulting package remains experimental and retains the source run, proposal, and learning journal as entry-bound evidence.  The proposer changes neither the source proof package nor its archived knowledge snapshot.

`promote` takes an experimental package and a selected forest, creates a new promoted package version, checks the resulting forest, builds every package-local Lean module, and asks Lean to resolve every advertised declaration.  It copies every selected package into a self-contained snapshot directory and leaves both the input forest and experimental package unchanged.  This gate covers package consistency and Lean source checks, while cross-artifact evaluation remains an explicit preceding review.  A later generation or reproof selects the new state through `--knowledge`.

The derived package may contain a checked lemma or tactic, prose guidance, or a worked proof example.  Checked Lean support becomes a theorem dependency when a later proof imports it, while guidance and examples influence proof construction without becoming premises of the artifact theorem.  Separate forest snapshots support independent project, experiment, and release histories from the same package collection.

```sh
tools/leanexegen learn record \
  -o knowledge-runs/demo-12 myprogram.proof
tools/leanexegen learn propose \
  -o knowledge-candidates/demo-12 myprogram.proof
tools/leanexegen learn promote \
  --forest knowledge/forest.json \
  -o knowledge-snapshots/demo-12 knowledge-candidates/demo-12
tools/leanexegen --knowledge knowledge-snapshots/demo-12/forest.json \
  -o next.wasm next.txt
```

## Headless Codex tasks

Each generative task starts at most one ephemeral `codex exec` session in its own directory below the repository's ignored `tmp/` root.  The invocation uses `-C`, `--sandbox workspace-write`, `--skip-git-repo-check`, `--ephemeral`, `--json`, `--output-schema`, and `-o`, with the prompt supplied on standard input.  Codex can inspect and edit files inside that task's workspace, but it cannot write elsewhere.

The artifact-proof workspace includes `PROOF_IMPORT_CHECK.js`, generated from the same proof-kit and generated-module allowlist used by outer acceptance.  Codex runs this check before every prescribed Lean build, so an unsupported direct import becomes an in-session diagnostic rather than a publication-time rejection.  Outer acceptance repeats the import audit independently on the returned source.

The outer process starts the complete Codex session through `tools/leanrun`, which holds the machine-wide Lean lock and places Codex and every child in one constrained cgroup.  A nested `tools/leanrun` invocation verifies the inherited memory and CPU limits before running Lean, Lake, or LeanExe, so it does not need another systemd scope.  The formal and proof sessions repeat one prescribed Lean build after each edit, while the program session repeats its Lean build, LeanExe report, and scratch compilation in sequence.

Codex returns one schema-validated `generated`, `questions`, or `problems` object after its internal work.  For `generated`, the orchestrator reads the candidate from the isolated workspace and repeats every final Lean or compiler check in a separate outer workspace.  A deterministic artifact starter that passes the full outer check needs no Codex session; an ordinary proof failure at the first Lean target starts the usual session, while runner, byte, audit, and later acceptance failures stop the stage.

| Task | Inputs visible to Codex | Required generated source |
|------|-------------------------|---------------------------|
| Formal specification | Request | A complete `FormalSpec` module defining `expected : Array UInt64 → Array UInt64` and `heapReserveBytes : Array UInt64 → Nat`; the orchestrator appends the representation and artifact predicates. |
| Lean program | Request and frozen `FormalSpec` | A complete `Source` module defining `compute : Array UInt64 → Array UInt64`, plus input-array and expected-output samples. |
| Artifact proof | Request, frozen `FormalSpec`, generated Talos `Program`, deterministic artifact-support modules, selected `PROOF_STRATEGIES.md`, structural `PROOF_TASK_FEATURES.json`, the task-filtered `KNOWLEDGE/` forest, the human `PROOF_LIBRARY.md` reference, and source mirrors for allowed proof modules | A complete `Behavior` module proving `artifact_behavior`; Source and the compiler are absent. |

The program task uses the formal file as specification context but does not import it into Source.  After compilation, the orchestrator copies the WASM and WAT into a frozen-artifact directory and removes the complete program workspace and every program-task outcome.  The artifact-proof task therefore receives no source file, source build object, or compiler output other than the frozen artifact model.

The [knowledge forest](ltg.md) contains separately versioned packages of checked proof assets, compiler-motif support, guidance, proof-generation methods, and worked examples.  Each package retains its own category JSONL indexes and canonical entries, while the forest selects the packages available to one run.  Every proof task receives an artifact-filtered forest view and the selected strategy guide, and schema-8 packages preserve the exact forest, package versions, package-local Lean sources, exclusions, and content digests used during proof generation.

`PROOF_KIT_SOURCE/` mirrors the allowed proof-kit modules inside the isolated task workspace.  The proving agent searches that bounded directory when a selected knowledge entry names a ProofKit declaration, while package-local modules appear at their Lean module paths and under the archived package.  The proof-kit source digest identifies the shared implementation, and the knowledge-task digest identifies every selected package-local source.

The [artifact-proof strategy notes](proof-strategies.md) describe proof structures distilled from accepted Talos proofs.  Leanexegen computes the export-reachable call graph from the frozen `Program`, records per-function instruction, local, loop, memory, arithmetic, and allocation features, and supplies only the matching marked sections.  The notes grant no imports and discharge no theorem; the generated `Behavior` module must contain every checked proof term used by the artifact theorem.

## Fixed array interface

The interface accepts and returns `Array UInt64`, and the compiled export is `compute`.  The formal Codex task defines `${namespace}.FormalSpec.expected : Array UInt64 → Array UInt64` and `${namespace}.FormalSpec.heapReserveBytes : Array UInt64 → Nat`; the latter bounds every bump-heap byte consumed above the initial heap top, including allocation headers, reserved capacity, intermediate allocations, and allocations retained at return.  The orchestrator appends the array representation, runtime precondition, and artifact property, then checks all three declarations before the formal source can freeze.

```lean
def UInt64ArrayAt (store : Wasm.Store Unit) (ptr : UInt64)
    (values : Array UInt64) : Prop :=
  ptr.toNat + 8 * (values.size + 1) ≤ 4294967296 ∧
  ptr.toNat + 8 * (values.size + 1) ≤ store.mem.pages * 65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size ∧
  ∀ (i : Nat), (h : i < values.size) →
    store.mem.read64
      (ptr + UInt64.ofNat (8 * (i + 1))).toUInt32 = values[i]

def RuntimeReady (initial : Wasm.Store Unit) (inputPtr : UInt64)
    (input : Array UInt64) : Prop :=
  UInt64ArrayAt initial inputPtr input ∧
  ∃ heapTop allocs retains releases frees : UInt64,
    initial.globals.globals =
      [.i64 heapTop, .i64 0, .i64 allocs, .i64 retains,
       .i64 releases, .i64 frees] ∧
    inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat ∧
    heapTop.toNat + 48 + 8 * ((expected input).size + 1) ≤ 4294967296 ∧
    heapTop.toNat + 48 + 8 * ((expected input).size + 1) ≤
      initial.mem.pages * 65536 ∧
    heapTop.toNat + heapReserveBytes input ≤ 4294967296 ∧
    heapTop.toNat + heapReserveBytes input ≤ initial.mem.pages * 65536 ∧
    initial.mem.pages ≤ 65536

def ArtifactSpec (module_ : Wasm.Module) : Prop :=
  ∃ entry, module_.findExport "compute" = some entry ∧
    ∀ (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit)
      (inputPtr : UInt64) (input : Array UInt64),
      RuntimeReady initial inputPtr input →
      Wasm.TerminatesWith env module_ entry initial [.i64 inputPtr]
        (fun final results => ∃ outputPtr,
          results = [.i64 outputPtr] ∧
          UInt64ArrayAt final outputPtr (expected input))
```

An array occupies one eight-byte length word followed by one eight-byte word per element.  `RuntimeReady` identifies the input array, fixes the allocator globals expected by generated LeanExe modules, places the bump pointer above the input, bounds the page count by WebAssembly's 65,536-page limit, and requires enough address space and existing memory for both the result representation and `heapReserveBytes input`.  The result predicate permits any output pointer whose final-memory representation equals `expected input`, while the source-free artifact proof must derive each allocation-capacity inequality from the formal reserve bound.

The reserve function forms part of the reviewed formal specification and may conservatively overestimate consumption.  Underestimating the artifact's allocation behavior makes the proof fail, as occurs when a filter reserves input-sized capacity but the bound accounts only for its smaller final result.  Neither the generated source nor a compiler assertion establishes the reserve: the theorem about the decoded artifact must prove that the stated precondition suffices.

The proof task must prove `${namespace}.Behavior.artifact_behavior : ${namespace}.FormalSpec.ArtifactSpec ${namespace}.module`.  Deterministic `ArtifactResult` source applies `artifact_correct_of` to that exact formal declaration and behavior theorem.  Neither a source theorem nor a compiler-lowering certificate participates in the resulting artifact theorem.

The `run` command provides the matching host interface.  It accepts zero or more unsigned decimal elements, allocates their array representation, invokes `compute`, and prints the decoded result array.  Generation records this command form in the proof package and uses the same host runner for checked samples.

```sh
tools/leanexegen run myprogram.wasm 10 20 30
```

## Proof package and independent verification

A successful command publishes `myprogram.wasm` and `myprogram.proof/`.  The sidecar contains its own `program.wasm`, the request, all three generated sources, deterministic artifact support, samples, host assumptions, tool pins, task reports, and a content index.  The generated Source appears for inspection and provenance, while the verification command builds only the formal specification, Talos program, artifact modules, behavioral proof, embedded-byte checker, and declaration audit.

Current generation and current-interface reproof publish schema 8, which archives the artifact-filtered knowledge forest supplied to the proof task.  Schema 7 archived one structured LTG catalog, and schema 6 introduced the `heapReserveBytes` formal interface without a catalog archive.  The verifier accepts schemas 3 through 8, preserving the recorded boundary of each historical package.

| Path | Contents |
|------|----------|
| `package.json` | Request identity, fixed formal interface, artifact declarations, warnings, verification command, and hashes for every other file. |
| `artifact.json` | WASM SHA-256 and length, export, invocation shape, fixed property, behavior theorem, and final artifact theorem. |
| `program.wasm` | The exact bytes embedded and proved by the generated Lean modules. |
| `request.txt` | The original prose request, including its original whitespace. |
| `interpretation.json` | The accepted summary and decisions from each generative task or deterministic artifact-proof path. |
| `stage-reports.json` | Per-task Codex versions, session bound, accepted source hashes, outer diagnostics, and a hash of each task report. |
| `proof-journal.md` | The artifact-proof agent's prose account, or the direct path's acceptance record.  The journal is diagnostic evidence and does not participate in the Lean proof. |
| `samples.json` | Input arrays, observed output arrays, and host-runner invocations used during generation. |
| `proof-library.md` | Human proof-kit documentation retained as part of the checked proof-kit source identity. |
| `proof-strategies.md` | The optional strategy sections selected for the frozen Talos program. |
| `proof-task-features.json` | The reachable call graph, structural features, selection reasons, extractor version, and strategy-source digest. |
| `knowledge-task.json` | Selected package versions, dependencies, artifact and derivative filters, entry exclusions, package-local Lean modules, and forest and package digests. |
| `knowledge/` | The task forest and each selected package's filtered catalog, retained evidence, manifest, and required Lean sources. |
| `ltg-task.json` and `ltg/` | The single-catalog task record retained by schema-7 packages. |
| `tool-pins.json` | Lean, Talos, proof-workspace, proof-kit-source, verifier-source, Node, `wasm-tools`, Wasmtime, and kernel-review identities. |
| `host-assumptions.json` | Host calls, store conditions, ABI expectations, or other assumptions recorded by the formal task. |
| `proof/LeanExeGen/...` | Formal specification, Source, Talos program, Behavior, deterministic artifact proof modules, byte checker, and axiom audit. |

An artifact-proof Codex task starts with `PROOF_JOURNAL.md` containing only its heading.  Its prompt asks Codex to update the prose after each Lean check and each significant change in approach, while leaving the form and organization to Codex.  Before an extended construction or elaboration attempt, the agent records the intended change and the residual goal that would demonstrate progress, which leaves useful evidence if the task later stalls.  Direct acceptance records the selected deterministic composition and successful checks instead; publication includes either journal's digest and excludes it from every Lean import and theorem dependency.

Verification validates the complete file set and every digest, recomputes every task-report and accepted-source hash, checks dependency pins, and checks the fixed formal declaration identity.  It checks the archived forest and package digests, category references, included entries, exclusions, evidence selection, module paths, and source imports, then installs the archived package-local Lean sources.  It creates a fresh formal declaration checker, byte-comparison module, and declaration-audit module before rebuilding the exact artifact theorem, checking each Git dependency and the Lean binary along the way.

```sh
tools/leanexegen verify myprogram.proof
```

Transient proof packages depend on the pinned repository package at `proofs/talos/lean`.  They set Lake 4.31.0's root-workspace `packagesDir` layout option to that proof workspace's existing `.lake/packages`, which reuses the pinned dependency checkouts.  A diagnostic transient package used this directory and completed a 3,014-job build through `tools/leanrun`; an earlier incomplete clone without the setting consumed 5.5 GB before removal.

## Acceptance evidence

On 2026-08-03, a live headless run processed the request, “Input and output are UInt64.  Return the input unchanged for every input.”  Each of the three Codex stages used one writable session with real checks under the inherited `tools/leanrun` scope, and each final candidate passed the independent outer check.  The proof stage received no Source module or compiler and proved both the behavioral theorem and the theorem for the exact embedded bytes.

The run published a 1,042-byte WASM file with SHA-256 `5561719e6bd6b2b56f2ca932ae16a5f6f518b615053bb766d8e473c4add0a725`.  Wasmtime received `-1` for the unsigned sample `18446744073709551615`, returned `-1`, and the sample shim reported the corresponding `UInt64` result.  A separate `tools/leanexegen verify` invocation accepted the sidecar and rebuilt `LeanExeGen.GeneratedRd3267f0041708ae6.Artifact.artifact_correct` without Codex or the compiler.

The controlled prime-factor reproof on 2026-08-03 retained the 1,348-byte artifact with SHA-256 `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`.  Byte comparisons confirmed that the formal specification, Source, Program, and every deterministic artifact module matched the input package, while Codex replaced `Behavior` and used both `wp_entry_to_loop` and `wp_entry_single_call`.  The behavior proof fell from 321 to 316 lines, controlled stage five took 390.849 seconds, and independent verification accepted the published artifact theorem.

## Trust boundary and limitations

The final theorem states the fixed formal property of the validated Talos translation of one embedded WASM byte sequence.  The sidecar binds that sequence to SHA-256, byte length, theorem names, task-source hashes, task reports, Lean 4.31.0, the Talos revision, the proof-workspace manifest, and the verifier-source digest.  The declaration audit rejects `sorryAx` and axioms outside the artifact gate's configured allowance.

Every successful generation prints four warnings: Codex interpreted the prose, no theorem connects Source to the formal specification, the theorem covers one exact digest under pinned semantics, and Codex generation and compilation remain outside the artifact proof.  These warnings also appear in `package.json`.  `-s` suppresses standard output but does not suppress warnings on standard error.

The current interface handles flat arrays of unsigned 64-bit words.  Richer element types, multiple exports, interactive question resolution, and source certificates remain future work.  Learning input is a validated successful proof package, while preserved failure records remain diagnostic files.  Automatic proposals currently produce standalone packages; manually composed packages may declare dependencies that forest and promotion checks enforce.  Generation can stop on Codex authentication, schema, stage timeout, compiler acceptance, internal check, outer check, or proof failures; independent verification of an existing sidecar has no Codex or compiler dependency.
