# Developing LeanExe

This guide defines the repository setup, development workflow, test gates, generated-file rules, and failure diagnostics.  The [Repository Overview](README.md) introduces the compiler, the [LeanExe User Manual](docs/manual.md) explains source authoring, and the [Language Specification](docs/spec.md) defines accepted behavior.  The [Development Plan](plan.md) is the current work queue, while the [Development Journal](devnotes.md) preserves decisions and test results.

## Prerequisites

LeanExe develops and tests on Linux.  The Wasmtime download script supports `x86_64` and `aarch64`; another platform requires a compatible Wasmtime CLI and C API supplied through the environment variables below.  A first proof build needs network access for the pinned Talos and Mathlib dependencies, and the semantic conformance gate needs CodeLib's pinned official WebAssembly testsuite submodule.

| Tool | Repository requirement |
|------|------------------------|
| Lean and Lake | Install through `elan`.  Both workspaces pin Lean 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`. |
| Proof Lean and Lake | The proof workspace records its matching pin in `proofs/talos/lean/lean-toolchain`.  `elan` selects it after entering that directory. |
| Wasmtime | `tools/download-wasmtime.sh` installs the default 44.0.0 CLI and C API under `build/tools/wasmtime` after checking the published SHA-256 hashes. |
| C compiler | A C11 compiler available as `cc` builds the Wasmtime host runner. |
| Node.js | Node 24.13.0 runs the test drivers.  `.node-version` records the exact version, and the complete runner checks it before building. |
| `wasm-tools` | Version 1.251.0 renders WAT for round-trip and Talos checks.  `.wasm-tools-version` records the exact version, and the source artifact and conformance gates check the selected executable. |
| System tools | The repository uses Bash or POSIX `sh`, `curl`, `sha256sum`, `tar`, `flock`, `systemd-run`, `nice`, `ionice`, `timeout`, and ordinary Unix file tools. |

The Talos revision is pinned in `proofs/talos/lean/lakefile.toml`, and its transitive Lean dependencies are pinned in the adjacent manifest.  `tools/check-node-version.js` enforces the Node pin, while `tools/check-wasm-tools-version.sh` enforces the `wasm-tools` pin selected through `WASM_TOOLS`, `PATH`, or `$HOME/.cargo/bin`.  The Wasmtime downloader checks both cached and downloaded archives before extraction and replaces a cached file only after its downloaded replacement passes verification.

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
| `tools/leanrun --timeout` | Time limit for one Lean, Lake, compiler, or verifier process.  The default is 900 seconds. |
| `tools/leanrun --lock-timeout` | Time limit in seconds for acquiring the machine-wide Lean slot.  The default is 900. |
| `LEANRUN_TOOLCHAIN` | Explicit Lean toolchain directory.  The default comes from the root `lean-toolchain` pin. |
| `WASM_TOOLS` | `wasm-tools` executable used by WAT and Talos checks. |
| `LEANEXE_FUZZ_CASES` | Case count for the ASCII validator fuzz test.  The default is 50. |

## Lean Process Limits

Lean and Lake can consume enough memory and CPU to make a workstation unresponsive, especially during a cold Mathlib build.  `tools/leanrun` places every direct `lean`, `lake`, `lean-wasm`, and Talos verifier command in the required user scope.  It also acquires the default `../vq` lock at `/tmp/vq-leanrun.<uid>/1`, which serializes Lean work across both repositories.

```sh
tools/leanrun --timeout <duration> <lean-or-lake-command>
```

The runner enforces `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and `LEAN_NUM_THREADS=1`.  `--timeout` bounds execution after lock acquisition, while `--lock-timeout` bounds the queue wait in seconds.  The corresponding `LEANRUN_TIMEOUT` and `LEANRUN_LOCK_TIMEOUT` environment variables remain available to repository drivers, but interactive commands use flags so `tools/leanrun` remains the stable approved prefix.  Stop if the user scope, lock, pinned toolchain, or required cgroup properties are unavailable, because another limit does not provide the same process boundary.

Repository Node drivers route Lean commands through `tools/leanrun`, and the Talos tools use the same runner for every Lean-based child.  Invoke `tools/talos-artifact.js`, `tools/talos-proof.js`, and `node test/run_all.js` directly because their children acquire the machine-wide slot.  A direct Lean or Lake command must name `tools/leanrun` as shown above.

## First Build

Install the runtime tools, build the compiler, build the native ABI runner, and run the execution suite from the repository root.  The download command writes only under the ignored `build` directory.  The suite rebuilds the compiler before running its Node drivers.

```sh
tools/download-wasmtime.sh
tools/leanrun lake build
tools/build-wasmtime-host.sh
node test/run_all.js
```

Initialize the proof workspace by running a focused Talos proof from the repository root.  The artifact stage fetches the pinned Talos dependency and builds its verifier when absent, then both stages populate ignored compiler and proof outputs.  A cold run may compile thousands of Lean jobs, while later runs reuse content-identical generated files and Lake outputs.

```sh
tools/talos-proof.js check gcd
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
| Extraction, IR, ownership, ABI, or WASM emission | Targeted fixture, `node test/run_all.js`, `tools/check-wat.sh`, and `tools/talos-proof.js check --all`. |
| Source-driven proof | `tools/talos-proof.js check <case>`, `tools/talos-proof.js check --all`, and the execution test for the source entry. |
| Exact-artifact proof | `tools/artifact-proof.js check <binary> <target>` and `tools/artifact-proof.js check-all`. |
| Talos semantics or conformance configuration | `node test/artifact_conformance.js` and `tools/artifact-conformance.js check`. |
| Toolchain or artifact-producing tool | Full execution and proof gates, artifact-byte review, version and checksum documentation, and trusted-base review. |

`node test/run_all.js` is the full execution gate.  It covers report classification, ownership reports, Wasmtime-only execution, core semantics, reference counting, allocation, ASCII strings, integer maps, JSON, WASI adapters, self-emission, standard Lean comparisons, IR comparisons, and fuzz cases.  `tools/check-wat.sh` checks that parsing compiler-emitted WAT produces the same bytes as direct binary emission.

## Proof Artifacts

The proof workspace has twenty registered source entries and twenty completed specifications, including all eight CLOB exports through `depth`.  `proofs/talos/cases.json` maps each source entry to its generated module and handwritten specification target, while `proofs/artifacts/registry.json` maps each frozen package to its exact-artifact proof target.  `tools/artifact-proof.js check-all` passed every frozen artifact theorem, behavioral specification, and manifest declaration on 2026-08-03 for the release-input identity recorded by that run; current release status comes from `tools/artifact-release.js inspect`.

`tools/talos-artifact.js prepare <case>` builds the source and compiler, emits ignored WASM and WAT, and asks the pinned Talos verifier to refresh the tracked `Project/<Case>/Program.lean` proof cache.  The tool gives Talos a disposable `rust/<case>/Cargo.toml` and artifact tree under the repository's ignored `tmp/` directory.  It replaces the three outputs only after generation succeeds, leaves a byte-identical cache untouched, and never edits handwritten proof modules.

`tools/talos-proof.js check <case>` performs the same generation into a temporary candidate, requires byte equality with the tracked program cache, then builds the registered specification target.  `tools/talos-proof.js check --all` checks all registered caches, compares the registry with `Project.lean` and `Project.Runtime.Checks`, and builds the complete proof library.  Neither check mode changes tracked cache files; `tools/talos-artifact.js prepare` provides the explicit refresh operation.

```sh
tools/talos-artifact.js prepare clob_cancel
tools/talos-proof.js check clob_cancel
tools/talos-proof.js check --all
tools/artifact-proof.js check-all
```

The [Verifying a Program](docs/verifying.md) guide covers stage inputs and outputs, registration, runtime pins, theorem statements, proof construction, and final-gate failures.  The [Talos Proofs](proofs/talos/README.md) document lists every completed theorem and its scope.  A new proof case is complete only when its registry flag, aggregate import, proof inventory, and recorded gate evidence agree.

After Lake fetches CodeLib, initialize the official testsuite pinned by that dependency.  The conformance command verifies the CodeLib revision, testsuite revision, `wasm-tools` version, Wasmtime version, exact filenames, and feature settings before execution.  It does not fetch or update third-party checkouts.

```sh
git -C proofs/talos/lean/.lake/packages/CodeLib submodule update --init vendor/testsuite
tools/artifact-conformance.js check
```

The current conformance command reports 3,853 Talos passes, six known assertion failures, and 627 skipped commands across twenty-five files.  Wasmtime passes all twenty-five selected files, while Talos's six failures come from imported-memory limit handling in `memory_grow.wast`.  The command accepts only the six configured rows as an upstream warning; no rows remove the warning, and any changed or additional failure stops the gate.

The same command extracts fifteen exact `assert_invalid` and `assert_malformed` modules from the pinned official corpus and checks their precise artifact decoder or validator errors.  It removes custom sections that `wasm-tools` adds while encoding text-origin `assert_invalid` modules because the accepted artifact profile rejects custom sections before reaching the intended validation rule.  It preserves raw `assert_malformed` binary modules byte-for-byte, and any missing command, changed line, changed classification stage, or changed error constructor stops the gate.

`proofs/artifacts/release.json` binds the artifact registry, each package manifest, every recorded theorem name, the tool pins, and the artifact and conformance results.  `tools/artifact-release.js inspect` validates those identities and derives the unresolved release conditions from the record.  `check-ready` fails while any condition remains.

`tools/artifact-release.js check-cold <revision>` clones the recorded source revision below the repository's ignored `tmp/` directory, compares its release inputs byte-for-byte with the recorded input identity, checks the external tools and exact Lean commit, fetches the pinned proof dependencies, initializes the official testsuite, and runs both release gates.  It rejects tracked changes after dependency setup or either gate, rechecks the input identity, and writes a machine-readable receipt after success.  The command requires a refreshed release identity, an immutable source revision containing that identity, and the recorded owner acceptance of the Lean 4.31.0 kernel defect.

## Generated Files and Dependencies

Root `.lake`, nested `.lake`, `build`, and `proofs/talos/.generated` contain ignored local output.  The repository tracks the twenty generated `Project/<Case>/Program.lean` proof caches because artifact-only verification and cold checkouts require the execution modules used by the behavioral theorems; Lean proves each cache equal to the translation of the decoded binary.  The nested official testsuite checkout lives below CodeLib's ignored `.lake` dependency tree, while `proofs/talos/conformance.json` records its required revision.  A Talos proof commit contains the source, tests, registry entry, runtime pins, aggregate import, generated program cache, and handwritten proof modules.  Inspect `git status` before and after generation: a changed `Program.lean` records a changed proof subject and requires artifact and proof review.

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
| Talos rejects generated WAT | Inspect the named decoder error and generated WAT, then reduce the unsupported emitted instruction or update the pinned Talos dependency through a separate reviewed change. |
| The Talos verifier is missing | Run either Talos tool with network access.  The artifact stage fetches the pinned dependency and builds the verifier under the required limits. |
| The aggregate Talos gate reports a proof error | Build the named specification or helper through the focused resource-limited boundary, then divide a no-diagnostic timeout before another attempt. |
| A proof build is unexpectedly large | Confirm that the process uses Lean 4.31.0 under the required limits.  A cold dependency build compiles thousands of jobs, while a long unchanged theorem requires a smaller elaboration boundary. |
| A generated model builds but a theorem fails | Treat the new instruction stream as the proof subject and repair `Spec.lean`; do not edit `Program.lean`. |

Failure messages should identify the command, module, entry, declaration, and rejected construct whenever those values exist.  Repository commands reserve stdout for requested reports and artifacts and stderr for failures.  A new CLI failure path must select one documented category and add a process-level status and stderr assertion.

## Documentation Maintenance

Each document has one role.  The repository overview provides a short introduction; this guide owns setup, development workflow, and gates; the manual owns source patterns and diagnostics; the specification owns semantics and rejection boundaries; the compiler reference owns implementation architecture; the Talos README owns the proof inventory; the verification guide owns proof procedure; the development plan owns future work; and the journal owns rationale and test evidence.  Update the authoritative document in the same change as the behavior it describes.

Update the authoritative document in the same change as the behavior it describes.  Keep volatile counts in one inventory and link to it elsewhere when the number adds no value.  Mark historical experiments and superseded plans at the top so a reader cannot mistake them for current procedure.
