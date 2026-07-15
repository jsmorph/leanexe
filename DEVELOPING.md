# Developing LeanExe

This guide defines the repository setup, development workflow, test gates, generated-file rules, and failure diagnostics.  The [Repository Overview](README.md) introduces the compiler, the [LeanExe User Manual](manual.md) explains source authoring, and the [Language Specification](spec.md) defines accepted behavior.  The [Development Plan](plan.md) is the current work queue, while the [Development Journal](devnotes.md) preserves decisions and test results.

## Prerequisites

LeanExe develops and tests on Linux.  The Wasmtime download script supports `x86_64` and `aarch64`; another platform requires a compatible Wasmtime CLI and C API supplied through the environment variables below.  A first proof build needs network access for the pinned Talos and Mathlib dependencies.

| Tool | Repository requirement |
|------|------------------------|
| Lean and Lake | Install through `elan`.  The compiler and proof workspaces pin Lean 4.31.0. |
| Proof Lean and Lake | The proof workspace records its matching pin in `proofs/talos-gcd/lean/lean-toolchain`.  `elan` selects it after entering that directory. |
| Wasmtime | `tools/download-wasmtime.sh` installs the default 44.0.0 CLI and C API under `build/tools/wasmtime` after checking the published SHA-256 hashes. |
| C compiler | A C11 compiler available as `cc` builds the Wasmtime host runner. |
| Node.js | Node 24.13.0 runs the test drivers.  `.node-version` records the exact version, and the complete runner checks it before building. |
| `wasm-tools` | Version 1.251.0 renders WAT for round-trip and Talos checks.  `.wasm-tools-version` records the exact version, and both artifact gates check the selected executable. |
| System tools | The setup and check scripts use Bash or POSIX `sh`, `curl`, `sha256sum`, `tar`, `cmp`, and ordinary Unix file tools. |

The Talos revision is pinned in `proofs/talos-gcd/lean/lakefile.toml`, and its transitive Lean dependencies are pinned in the adjacent manifest.  `tools/check-node-version.js` enforces the Node pin, while `tools/check-wasm-tools-version.sh` enforces the `wasm-tools` pin selected through `WASM_TOOLS`, `PATH`, or `$HOME/.cargo/bin`.  The Wasmtime downloader checks both cached and downloaded archives before extraction and replaces a cached file only after its downloaded replacement passes verification.

These environment variables configure local executables and the Wasmtime downloader.  Set them in the invoking environment rather than committing machine-specific paths.  Include the relevant values in a failure report when a nondefault executable or release source may affect the result.

| Variable | Meaning |
|----------|---------|
| `WASMTIME` | Wasmtime CLI used by tests and comparison tools. |
| `WASMTIME_C_API` | Directory containing `include/wasmtime.h` and `lib/libwasmtime.so`. |
| `WASMTIME_VERSION` | Wasmtime release version downloaded by the setup script.  The default is 44.0.0. |
| `WASMTIME_PLATFORM` | Release platform name.  Automatic detection supports `aarch64-linux` and `x86_64-linux`. |
| `WASMTIME_BASE_URL` | Release mirror containing archives with the standard Wasmtime filenames. |
| `WASMTIME_CLI_SHA256` | Expected CLI archive hash.  Required with an override that has no checked built-in hash. |
| `WASMTIME_C_API_SHA256` | Expected C API archive hash.  Required with an override that has no checked built-in hash. |
| `LEANEXE_WASMTIME_HOST` | Compiled C host runner used by ABI tests. |
| `LEAN_WASM_EXE` | `lean-wasm` executable used by Node tests. |
| `WASM_TOOLS` | `wasm-tools` executable used by WAT and Talos checks. |
| `LEANEXE_FUZZ_CASES` | Case count for the ASCII validator fuzz test.  The default is 50. |

## Lean Process Limits

Lean and Lake can consume enough memory and CPU to make a workstation unresponsive, especially during a cold Mathlib build.  Run every `lean`, `lake`, and `lean-wasm` command in one resource-limited user scope, including a script such as `test/run_all.js` or `tools/check-talos.sh` that starts those commands.  Never run two Lean or Lake processes concurrently.

```sh
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout <duration> <command>
```

Choose a duration that bounds the named test or build without terminating expected work.  `CPUQuota=100%` limits the complete scope to one CPU core because Lake 5.0.0 has no job-count option.  Stop if the user scope or required cgroup properties are unavailable, because an address-space limit does not provide the same memory control.  Use each command shown in the following sections as the `<command>` payload in this wrapper.

## First Build

Install the runtime tools, build the compiler, build the native ABI runner, and run the execution suite from the repository root.  The download command writes only under the ignored `build` directory.  The suite rebuilds the compiler before running its Node drivers.

```sh
tools/download-wasmtime.sh
lake build
tools/build-wasmtime-host.sh
node test/run_all.js
```

Initialize the proof workspace separately with `tools/setup-talos.sh` from the repository root.  The script fetches pinned dependencies and builds `Project`, so a cold run may compile thousands of Lean jobs while later runs reuse `.lake` outputs.  Building the verifier remains a separate step required only for an intentional `--update` of a checked-in artifact.

```sh
tools/setup-talos.sh
cd proofs/talos-gcd/lean/.lake/packages/CodeLib/verifier
lake build
```

## Development Workflow

Start a change by reducing it to the smallest source example or failing test that exposes the behavior.  Build the affected Lean module before invoking `lean-wasm`, because extraction loads checked declarations from `.lake/build/lib/lean`.  Record design rationale, authoritative references, failed approaches, and completed gate results in the development journal.

Use the compiler diagnostics in the order below.  Each command reads the same checked declaration but answers a different question.  Preserve the first specific failure instead of replacing it with a later, less informative symptom.

| Command | Purpose |
|---------|---------|
| `report --module <module> --entry <entry>` | Classify the entry and its reachable declarations, stopping at specific unsupported source. |
| `dump-ir --module <module> --entry <entry>` | Print the extracted IR when evaluation order, lowering, or statement placement is in question. |
| `ownership-report --module <module> --entry <entry>` | Print owner slots, fresh-result summaries, emitted releases, returned owners, and explicit release expressions. |
| `eval-ir --module <module> --entry <entry> [arg ...]` | Run a scalar entry in the reference IR interpreter when the entry lies in its fragment. |
| `compile-wat --module <module> --entry <entry> --out <path>` | Inspect the WAT emitted from the same structured module as the binary encoder. |

Runtime-intrinsic entries require a separate comparison boundary.  Ordinary Lean and the reference IR interpreter treat `LeanExe.Runtime` counters and release as zero-valued no-ops, while generated WASM updates allocator state and recursively releases marked owners.  Test intrinsic results with Wasmtime, inspect the source judgment with `ownership-report`, and use the Talos runtime theorems when the claim depends on emitted release behavior.

The release checker accepts direct fresh allocations, roots returned fresh by an existing helper summary, and statically owner-zero arrays at final use.  It rejects aliases, later use, repeated release, branch-dependent or conditional ownership, fields, parameters, and heap-bearing escapes.  Treat such a rejection as an ownership-analysis requirement; `JsonMergeTreeCommand.makeMergedTree` and `JsonGcTreeRewrite.transform` remain reduced examples of two deferred shapes.

Run the smallest relevant test during development, then run every gate required by the changed boundary before considering the work complete.  The repository has no remote CI configuration, so local gate results are the available evidence.  Do not replace Wasmtime execution with JavaScript WASM execution; `test/no_js_wasm_execution.js` enforces that rule.

| Change | Required checks |
|--------|-----------------|
| Documentation only | `git diff --check`, local-link review, and command review for every changed example. |
| Source example | Targeted `lake build`, the relevant Node test, and a standard-Lean comparison when the entry has an observable reference result. |
| Extraction, IR, ownership, ABI, or WASM emission | Targeted fixture, `node test/run_all.js`, `tools/check-wat.sh`, and `tools/check-talos.sh`. |
| Artifact proof | The per-case Talos script, `tools/setup-talos.sh`, `tools/check-talos.sh`, and the execution test for the source entry. |
| Toolchain or artifact-producing tool | Full execution and proof gates, artifact-byte review, version and checksum documentation, and trusted-base review. |

`node test/run_all.js` is the full execution gate.  It covers report classification, ownership reports, Wasmtime-only execution, core semantics, reference counting, allocation, ASCII strings, integer maps, JSON, WASI adapters, self-emission, standard Lean comparisons, IR comparisons, and fuzz cases.  `tools/check-wat.sh` checks that parsing compiler-emitted WAT produces the same bytes as direct binary emission.

## Proof Artifacts

The proof workspace contains sixteen checked artifacts with completed specifications.  `proofs/talos-gcd/rust/build/<case>/program.wasm` and `program.wat` are checked-in proof inputs, `Project/<Case>/Program.lean` is generated by the Talos verifier emitter, and `Project/<Case>/Spec.lean` is handwritten.  Never edit a generated `Program.lean` file.

A normal per-case check recompiles the Lean entry, regenerates temporary WASM and WAT, compares both files with the checked-in inputs, and builds the handwritten proof.  Its `--artifacts-only` mode stops after the byte comparisons.  A byte mismatch is a failed gate until its cause is understood.

The aggregate gate invokes every case in artifact-only mode before consulting the proof workspace, so the first changed artifact appears before any proof output.  It then runs Lake with `--no-build` and succeeds only when the complete `Project` target is current.  If proof dependencies or outputs are missing or stale, run `tools/setup-talos.sh` separately and repeat the gate.

```sh
tools/check-talos-clob-cancel.sh
tools/check-talos.sh --artifacts-only
tools/setup-talos.sh
tools/check-talos.sh
```

Use `--update` only after deciding that changed compiler output is intended.  The update transaction replaces the checked-in WASM and WAT, regenerates `Program.lean`, and builds the case proof; on failure, the script restores the previous files.  Review the artifact diff and repair the handwritten theorem before committing the change.

```sh
tools/check-talos-clob-cancel.sh --update
```

The [Verifying a Program](verifying.md) guide covers registration, runtime pins, theorem statements, and proof construction.  The [Talos Proofs](proofs/talos-gcd/README.md) document lists every current theorem and its scope.  A new proof case is incomplete until both documents reflect it and the aggregate script includes it.

## Generated Files and Dependencies

Root `.lake`, nested `.lake`, and `build` directories contain ignored local output.  The WASM, WAT, and `Program.lean` files under the proof workspace are tracked because they connect a theorem to the emitted artifact.  Inspect `git status` before and after any generator command so unrelated local files do not enter the change.

Keep third-party dependencies to a minimum and discuss a new dependency before adding it.  Pin a dependency or artifact-producing tool to an immutable version, record its purpose and trusted-base effect, and add the required gate.  An update to Talos, Lean, Wasmtime, or `wasm-tools` requires review of generated bytes and proof assumptions.

## CLI Failure Interface

`lean-wasm` reserves stdout for requested reports and values, while compiler artifacts go to the path named by `--out`.  Every handled failure writes a record beginning `lean-wasm: <category>:` to stderr, followed by the command and available module, entry, and output-path context.  The detailed cause retains the extractor or operating-system message.

| Status | Category | Meaning |
|--------|----------|---------|
| `2` | `usage` | The command shape, numeric syntax, or configured bound is invalid. |
| `3` | `source` | The module or entry cannot be loaded, the entry type is wrong, the source lies outside the accepted subset, or IR evaluation lies outside its supported fragment. |
| `4` | `I/O` | Reading or writing the requested process stream or output path failed. |
| `5` | `internal` | An encoder invariant failed or an exception escaped an operation-specific boundary. |

Handled failures do not print Lean's `uncaught exception` prefix.  The CLI emits no ANSI escapes, so stderr remains stable for scripts and logs.  `test/cli_errors.js` checks malformed arguments, invalid and excessive bounds, missing modules and entries, wrong entry types, unsupported declarations, reserved export names, failed output writes, help output, and the expected statuses for those reachable failures.

## Troubleshooting

| Failure | Diagnosis and response |
|---------|------------------------|
| `wasmtime` is missing | Run `tools/download-wasmtime.sh`, or set `WASMTIME` to a compatible executable. |
| The C host runner is missing | Run `tools/build-wasmtime-host.sh`.  If the C API is outside the default tree, set `WASMTIME_C_API` first. |
| `wasm-tools` is missing | Install the required executable and set `WASM_TOOLS`, or place it in `PATH` or `$HOME/.cargo/bin`. |
| A module or entry cannot be loaded | Build the named module with Lake, then confirm that the fully qualified entry name matches the checked declaration. |
| `report` rejects a declaration | Read the first rejected dependency and use the source forms in the user manual.  Do not hide the dependency with unsafe code, dummy effects, or host assumptions. |
| A Talos check stops at `cmp` | Regenerate temporary output through the same script and determine which source, compiler, runtime, or tool change moved the bytes.  Use `--update` only when that change is intended. |
| The Talos verifier is missing | Build `proofs/talos-gcd/lean/.lake/packages/CodeLib/verifier` before running a case with `--update`. |
| The aggregate Talos gate reports missing or stale proof outputs | Run `tools/setup-talos.sh` under the required process limits, then repeat `tools/check-talos.sh`. |
| A proof build is unexpectedly large | Confirm that `tools/setup-talos.sh` is running with Lean 4.31.0 under the required process limits.  A cold dependency build compiles thousands of jobs. |
| A generated model builds but a theorem fails | Treat the new instruction stream as the proof subject and repair `Spec.lean`; do not edit `Program.lean`. |

Failure messages should identify the command, module, entry, declaration, and rejected construct whenever those values exist.  Repository commands reserve stdout for requested reports and artifacts and stderr for failures.  A new CLI failure path must select one documented category and add a process-level status and stderr assertion.

## Documentation Maintenance

Each document has one role.  The repository overview provides setup and a user-facing introduction; this guide owns development workflow and gates; the manual owns source patterns and diagnostics; the specification owns semantics and rejection boundaries; the Talos README owns the current proof inventory; the verification guide owns proof procedure; the development plan owns future work; and the journal owns history and rationale.  The technical summary explains architecture without serving as a second roadmap.

Update the authoritative document in the same change as the behavior it describes.  Keep volatile counts in one inventory and link to it elsewhere when the number adds no value.  Mark historical experiments and superseded plans at the top so a reader cannot mistake them for current procedure.
