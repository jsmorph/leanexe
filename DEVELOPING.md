# Developing LeanExe

This guide defines the repository setup, development workflow, test gates, generated-file rules, and failure diagnostics.  The [Repository Overview](README.md) introduces the compiler, the [LeanExe User Manual](docs/manual.md) explains source authoring, and the [Language Specification](docs/spec.md) defines accepted behavior.  The [Development Plan](plan.md) is the current work queue, while the [Development Journal](devnotes.md) preserves decisions and test results.

## Prerequisites

LeanExe develops and tests on Linux, with local execution support for ARM macOS.
The Linux Wasmtime download script supports `x86_64` and `aarch64`; ARM Macs
use the pinned repository-local bootstrap below.  A first proof build needs
network access for the pinned Talos and Mathlib dependencies, and the semantic
conformance gate needs CodeLib's pinned official WebAssembly testsuite submodule.

On an ARM Mac, run these commands from the repository root:

```sh
sh tools/bootstrap-macos.sh
source tools/macos-env.sh
tools/leanrun --timeout 15m lake build lean-wasm
```

The bootstrap verifies official archive SHA-256 digests and installs the same
Lean, Node, wasm-tools, and Wasmtime versions under `build/tools`.  It preserves
existing archives and installation directories.  The environment script selects
those paths without changing global installations.  The Darwin runner uses
native `flock`, a process-group timeout, one Lean thread, and nice priority.
It requires explicit local mode because systemd cgroups and `ionice` are
unavailable.  If a sandbox blocks `nice`, it stops unless the user has expressly
authorized `LEANRUN_INHERIT_PRIORITY=1`; that exception retains inherited
priority and prints a diagnostic. `tools/macos-env.sh` selects local mode and
the inherited-priority setting; use that configuration only in an environment
where those exceptions are explicitly authorized. The Linux `/proc`
compatibility preload is not used on macOS.

| Tool | Repository requirement |
|------|------------------------|
| Lean and Lake | Use `elan` on Linux or the repository bootstrap on ARM macOS. The compiler root pins exact Lean 4.34.0-rc2 at commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`. |
| Proof Lean and Lake | The proof workspace records its exact Lean 4.34.0-rc2 pin in `proofs/talos/lean/lean-toolchain`; its Lake files pin Talos revision `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`. |
| Wasmtime | `tools/download-wasmtime.sh` installs the default 44.0.0 CLI and C API under `build/tools/wasmtime` after checking the published SHA-256 hashes. |
| C compiler | A C11 compiler available as `cc` builds the Wasmtime host runner. |
| Node.js | Node 24.13.0 runs the test drivers.  `.node-version` records the exact version, and the complete runner checks it before building. |
| `wasm-tools` | Version 1.251.0 renders WAT for round-trip and Talos checks.  `.wasm-tools-version` records the exact version, and the source artifact and conformance gates check the selected executable. |
| System tools | The repository uses Bash or POSIX `sh`, `curl`, `sha256sum`, `tar`, `flock`, `nice`, `ionice`, `timeout`, and ordinary Unix file tools.  Standard runner mode also requires `systemd-run`. |

The Talos revision is pinned in `proofs/talos/lean/lakefile.toml`, and its transitive Lean dependencies are pinned in the adjacent manifest.  `tools/check-node-version.js` enforces the Node pin, while `tools/check-wasm-tools-version.sh` enforces the `wasm-tools` pin selected through `WASM_TOOLS`, `PATH`, or `$HOME/.cargo/bin`.  It accepts both the compact Cargo-style version line and the official release binary's additional well-formed commit/date metadata, while requiring the exact pinned numeric version.  The Wasmtime downloader checks both cached and downloaded archives before extraction and replaces a cached file only after its downloaded replacement passes verification.

These environment variables configure local executables and the Wasmtime downloader.  Set them in the invoking environment rather than committing machine-specific paths.  Include the relevant values in a failure report when a nondefault executable or release source may affect the result.

| Variable | Meaning |
|----------|---------|
| `CC` | C compiler for the Euler comparison tests; defaults to `cc`. ARM macOS can use `gcc-15` to meet its advertised IEEE arithmetic checks. |
| `WASMTIME` | Wasmtime CLI used by tests and comparison tools. |
| `WASMTIME_C_API` | Directory containing `include/wasmtime.h` and the library: `lib/libwasmtime.so` on Linux or `lib/libwasmtime.dylib` on macOS. |
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
| `LEANRUN_LOCAL=1` | Explicitly user-authorized fallback when no systemd user scope exists.  It retains serialization, the pinned toolchain, one Lean thread, priority settings, and timeout, but not memory, swap, or CPU cgroup enforcement. |
| `WASM_TOOLS` | `wasm-tools` executable used by WAT and Talos checks. |
| `LEANEXE_FUZZ_CASES` | Case count for the ASCII validator fuzz test.  The default is 50. |

Both the ordinary C host runner and the byte-I/O host use Cranelift with
Wasmtime's NaN canonicalization enabled.
This execution mode matches the canonical arithmetic NaNs in the Lean and
Talos floating-point models.  `node test/f32_bits.js` checks exact Wasmtime
NaN words, including signaling inputs and noncanonical payloads.
`node test/byte_io.js` also checks binary32 and binary64 NaNs through compiled
byte-I/O entries. The
[Wasmtime configuration reference](https://docs.wasmtime.dev/c-api/config_8h.html)
documents `wasmtime_config_cranelift_nan_canonicalization_set`.

The pretrained GPT-2 commands require `uv` and use the project in
`training/gpt2`.  Its lockfile preserves the approved PyTorch and Transformers
versions and their dependencies.  `tools/gpt2` runs WASM inference, and
`tools/gpt2-pytorch` runs the CPU reference with the same generation defaults.
Both create or update `training/gpt2/.venv` through `uv run`.
The [GPT-2 instructions](data/gpt2-124m/README.md) include checkpoint setup
and direct Python one-liners.  Tests in `test/packed.js` use the same project.

## Lean Process Limits

Lean and Lake can consume enough memory and CPU to make a workstation unresponsive, especially during a cold Mathlib build.  In standard mode `tools/leanrun` places every direct `lean`, `lake`, `lean-wasm`, and Talos verifier command in the required user scope.  It always acquires the default `../vq` lock at `/tmp/vq-leanrun.<uid>/1`, which serializes Lean work across both repositories.

```sh
tools/leanrun --timeout <duration> <lean-or-lake-command>
```

Standard mode enforces `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and `LEAN_NUM_THREADS=1`.  `--timeout` bounds execution after lock acquisition, while `--lock-timeout` bounds the queue wait in seconds.  The corresponding `LEANRUN_TIMEOUT` and `LEANRUN_LOCK_TIMEOUT` environment variables remain available to repository drivers, but interactive commands use flags so `tools/leanrun` remains the stable approved prefix.  Stop if the user scope, lock, pinned toolchain, or required cgroup properties are unavailable.  Only after the user explicitly authorizes execution without the systemd cgroup may `LEANRUN_LOCAL=1` be used; it retains the lock, pinned toolchain, timeout, `LEAN_NUM_THREADS=1`, `nice`, and `ionice`, while clearly warning that the cgroup limits are absent.

Set `LEANRUN_LOCAL=1` on a runner-calling repository driver and invoke that
driver directly.  Do not place the driver beneath `tools/leanrun` or invoke
`tools/leanrun` recursively in local mode: the outer process holds the same
non-reentrant lock required by the child, and the runner rejects this nesting.

```sh
LEANRUN_LOCAL=1 tools/talos-artifact.js prepare <case>
```

Repository Node drivers route Lean commands through `tools/leanrun`, and the Talos tools use the same runner for every Lean-based child.  Invoke `tools/talos-artifact.js`, `tools/talos-proof.js`, and `node test/run_all.js` directly because their children acquire the machine-wide slot.  A direct Lean or Lake command must name `tools/leanrun` as shown above.

## First Build

On Linux, install the pinned Wasmtime CLI and C API:

```sh
tools/download-wasmtime.sh
```

On ARM macOS, use the bootstrap and environment script in
[Prerequisites](#prerequisites). In either configured environment, build the
compiler and native ABI runner from the repository root:

```sh
tools/leanrun --timeout 15m lake build lean-wasm
tools/build-wasmtime-host.sh
```

Run `node test/run_all.js` for the complete execution suite. Its drivers build
the source modules they need. During development, use the focused checks below
for the affected behavior.

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

Run the smallest relevant test during development, then run every gate required by the changed boundary before considering the work complete.  The repository has no remote CI configuration, so local gate results are the available evidence.  Wasmtime remains the execution engine for the existing runtime suite. The arithmetic compiler theorem also has an independent Node/V8 comparison in `test/arithmetic_engine.mjs`; this is the sole additional engine exception allowed by `test/no_js_wasm_execution.js`.

| Change | Required checks |
|--------|-----------------|
| Documentation only | `git diff --check`, `tools/check-docs.js`, and command review for every changed example. |
| Source example | Targeted `lake build`, the relevant Node test, and a standard-Lean comparison when the entry has an observable reference result. |
| Extraction, IR, ownership, ABI, or WASM emission | Targeted fixture, `node test/run_all.js`, `tools/check-wat.sh`, and `tools/talos-proof.js check --all`. |
| Source-driven proof | `tools/talos-proof.js check <case>`, `tools/talos-proof.js check --all`, and the execution test for the source entry. |
| Exact-artifact proof | `tools/artifact-proof.js check <binary> <target>` and `tools/artifact-proof.js check-all`. |
| Proof knowledge package or forest | `tools/ltg check`, `tools/knowledge check`, `node test/ltg.js`, `node test/knowledge.js`, and `node test/leanexegen.js`; package-local Lean source also requires `tools/leanrun --timeout 20m node test/knowledge.js --lean`. |
| Talos semantics or conformance configuration | `node test/artifact_conformance.js` and `tools/artifact-conformance.js check`. |
| Toolchain or artifact-producing tool | Full execution and proof gates, artifact-byte review, version and checksum documentation, and trusted-base review. |

The arithmetic compiler theorem has focused checks: `tools/arithmetic-check.js proof`
builds its general theorem and audits all nine declarations; `tools/arithmetic-check.js engine`
compares the real compiler's emitted modules with native Lean. See
[Arithmetic compiler correctness](docs/arithmetic-correctness.md) for prerequisites,
scope and standalone package verification. Run affected checks incrementally;
there is no requirement to repeat unrelated full suites after every update.

`node test/run_all.js` is the full execution gate.  It covers report classification, ownership reports, Wasmtime-only execution, core semantics, reference counting, allocation, ASCII strings, integer maps, JSON, WASI adapters, self-emission, standard Lean comparisons, IR comparisons, and fuzz cases.  `tools/check-wat.sh` checks that parsing compiler-emitted WAT produces the same bytes as direct binary emission.

For byte I/O, build `LeanExe.Examples.ByteIO` and run `node test/wasi_io_host.js`, `node test/byte_io.js`, and `node test/refcount.js`.  The I/O drivers build `tools/wasi-io-host.c` against the pinned Wasmtime C API.  Set `WASMTIME_C_API` when using an external installation; `LEANEXE_WASI_IO_HOST` selects the compiled host.  The source tests validate each generated module with `WASM_TOOLS` and exercise actual nonblocking pipes, delayed input, partial writes, deadlines, retained buffers, and allocation counts.  The ordinary Wasmtime CLI is suitable for the pure WASI adapters but cannot supply this byte-I/O host contract.  Existing Talos checks validate registered pure programs after shared compiler changes; run `tools/byte-io-proof.js check` for the separately specified byte-I/O host contracts, protocol laws, and exact-binary execution cases. The [byte-I/O verification boundary](proofs/byte-io/README.md) describes the host and clock-progress assumptions. This gate compares fresh compiler output with the proof fixture, checks decoding and validation in Lean, and rejects axioms beyond the standard three logical axioms.

The experimental self-hosted emitter is deliberately outside the aggregate gate.
Run `node test/selfhost_emitter.js` separately only for a change to the module-image
codec, emitter, or bootstrap boundary; it does not block native compiler work.

## Proof Artifacts

The proof workspace covers programs including FP32 and quantized GPT-2 cached
sessions, CLOB operations, numerical kernels, and complete Euler solvers.
[The theorem inventory](proofs/talos/README.md) identifies each public claim and
its assumptions. Source-driven proofs and exact-artifact proofs have distinct
inputs:

- `proofs/talos/cases.json` maps source entries to generated execution models and
  registered behavioral specifications.
- `proofs/artifacts/registry.json` maps packaged binary identities to their
  exact-artifact proof targets. A theorem for one hash does not cover a different
  compiler output.

Numerical claims add real-arithmetic contracts to execution theorems. For
example, the [Euler step dataset](data/euler-rusanov-step-v1/README.md) connects
exact output words to checked real values and rounding bounds. Reproduce its
rational comparison, CSV, and plot with `node tools/euler-rusanov-step-data.js check`.
Host and C comparisons are execution tests; the Lean theorem states the formal
boundary. Floating-point examples use compiler-recognized raw-word intrinsics,
not general Lean `Float` source.

`tools/talos-artifact.js prepare <case>` builds the source and compiler, emits ignored WASM and WAT, and asks the pinned Talos verifier to refresh the tracked `Project/<Case>/Program.lean` proof cache.  The tool creates a fresh uniquely named `tmp/leanexe-talos-*` staging directory inside the repository, gives Talos a disposable `rust/<case>/Cargo.toml` and artifact tree there, and removes only that same newly created staging directory before returning.  It never treats pre-existing `tmp/` entries as cleanup targets.  It replaces the three requested outputs only after generation succeeds, leaves a byte-identical cache untouched, and never edits handwritten proof modules.  Under the local operating envelope, invoke this Node driver directly: it invokes `tools/leanrun` for its own children, and an outer `tools/leanrun` wrapper is rejected as a nested runner.

`tools/talos-proof.js check <case>` performs the same generation into a temporary candidate, requires byte equality with the tracked program cache, then builds the registered specification target.  `tools/talos-proof.js check --all` checks all registered caches, compares the registry with `Project.lean` and `Project.Runtime.Checks`, builds each completed specification under its fifteen-minute limit, and then builds the complete proof library.  Neither check mode changes tracked cache files; `tools/talos-artifact.js prepare` provides the explicit refresh operation.

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

A cold conformance run builds the direct imports of Mathlib's pinned `Mathlib.Tactic` umbrella in fixed-size groups, then builds the testsuite library and executable as separate targets.  Each group has its own process limit, so the initial dependency compilation does not share one timeout with the complete import graph and final executable link.  The conformance driver reads this target list from the checked-out pinned Mathlib source rather than maintaining another dependency inventory.

The conformance gate runs the configured execution corpus in Wasmtime and Talos. Its checked configuration names permitted skips; unexpected failures or skips fail the check.

The same command extracts the configured `assert_invalid` and `assert_malformed` modules from the pinned official corpus and checks their precise artifact decoder or validator errors.  The tool removes custom sections added by `wasm-tools` when encoding text-origin invalid modules because the accepted artifact profile rejects those sections before the intended validation rule.  It preserves raw malformed binary modules byte-for-byte and rejects any changed command, classification stage, or error constructor.

Release records are a separate packaging workflow. `proofs/artifacts/release.json`
binds registry entries, manifests, theorem names, tool pins, and gate results.
`tools/artifact-release.js inspect` checks those identities and reports the
record's unresolved conditions. Use the [artifact format guide](docs/artifact-format.md)
for release recording and separate-checkout reproduction when that workflow is
requested. Ordinary development uses the checks for its affected boundary.

## Generated Files and Dependencies

Root `.lake`, nested `.lake`, `build`, and `proofs/talos/.generated` contain ignored local output.  The repository tracks the generated `Project/<Case>/Program.lean` proof caches listed in the source registry because source-driven verification and cold checkouts require the execution modules used by the behavioral theorems; for each exact-artifact package, Lean additionally proves its cache equal to the translation of the decoded frozen binary.  The nested official testsuite checkout lives below CodeLib's ignored `.lake` dependency tree, while `proofs/talos/conformance.json` records its required revision.  A Talos proof commit contains the source, tests, registry entry, runtime pins, aggregate import after completion, generated program cache, and handwritten proof modules.  Inspect `git status` before and after generation: a changed `Program.lean` records a changed proof subject and requires artifact and proof review.

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
| A proof build is unexpectedly large | Confirm that the process uses the exact toolchain pinned by its workspace under the required limits.  A cold dependency build compiles thousands of jobs, while a long unchanged theorem requires a smaller elaboration boundary. |
| A generated model builds but a theorem fails | Treat the new instruction stream as the proof subject and repair `Spec.lean`; do not edit `Program.lean`. |

Failure messages should identify the command, module, entry, declaration, and rejected construct whenever those values exist.  Repository commands reserve stdout for requested reports and artifacts and stderr for failures.  A new CLI failure path must select one documented category and add a process-level status and stderr assertion.

## Documentation Maintenance

Each document has one role.  The repository overview provides a short introduction; this guide owns setup, development workflow, and gates; the manual owns source patterns and diagnostics; the specification owns semantics and rejection boundaries; the compiler reference owns implementation architecture; the Talos README owns the proof inventory; the verification guide owns proof procedure; the development plan owns future work; and the journal owns rationale and test evidence.  Update the authoritative document in the same change as the behavior it describes.

Write maintained guides in terms of current behavior, commands, and proof boundaries. Keep volatile counts and measurement details in the relevant inventory or evidence package and link to them. Review changed command examples against their implementations, and keep exact-binary claims tied to the corresponding manifest.
