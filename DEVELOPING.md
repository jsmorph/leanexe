# Developing LeanExe

This guide defines the repository setup, development workflow, test gates, generated-file rules, and failure diagnostics.  The [Repository Overview](README.md) introduces the compiler, the [LeanExe User Manual](manual.md) explains source authoring, and the [Language Specification](spec.md) defines accepted behavior.  The [Development Plan](plan.md) is the current work queue, while the [Development Journal](devnotes.md) preserves decisions and test results.

## Prerequisites

LeanExe develops and tests on Linux.  The Wasmtime download script supports `x86_64` and `aarch64`; another platform requires a compatible Wasmtime CLI and C API supplied through the environment variables below.  A first proof build needs network access for the pinned Talos and Mathlib dependencies.

| Tool | Repository requirement |
|------|------------------------|
| Lean and Lake | Install through `elan`.  The root `lean-toolchain` pins Lean 4.29.1. |
| Proof Lean and Lake | The proof workspace pins Lean 4.31.0 in `proofs/talos-gcd/lean/lean-toolchain`.  `elan` selects it after entering that directory. |
| Wasmtime | `tools/download-wasmtime.sh` installs the default 44.0.0 CLI and C API under `build/tools/wasmtime`. |
| C compiler | A C11 compiler available as `cc` builds the Wasmtime host runner. |
| Node.js | Node runs the test drivers.  The repository does not yet pin a compatible version. |
| `wasm-tools` | The WAT round-trip and Talos checks require `wasm-tools`.  The repository does not yet pin a compatible version. |
| System tools | The setup and check scripts use Bash or POSIX `sh`, `curl`, `tar`, `cmp`, and ordinary Unix file tools. |

The Talos revision is pinned in `proofs/talos-gcd/lean/lakefile.toml`, and its transitive Lean dependencies are pinned in the adjacent manifest.  Node and `wasm-tools` remain known reproducibility gaps, so record `node --version` and `wasm-tools --version` when reporting a tool-dependent failure.  The Wasmtime download script currently relies on HTTPS release downloads without checking archive hashes; the development plan tracks checksum verification.

These environment variables replace repository defaults when local tools live elsewhere.  Set them in the invoking environment rather than committing machine-specific paths.  Include the relevant values in a failure report when a nondefault executable may affect the result.

| Variable | Meaning |
|----------|---------|
| `WASMTIME` | Wasmtime CLI used by tests and comparison tools. |
| `WASMTIME_C_API` | Directory containing `include/wasmtime.h` and `lib/libwasmtime.so`. |
| `LEANEXE_WASMTIME_HOST` | Compiled C host runner used by ABI tests. |
| `LEAN_WASM_EXE` | `lean-wasm` executable used by Node tests. |
| `WASM_TOOLS` | `wasm-tools` executable used by WAT and Talos checks. |
| `LEANEXE_FUZZ_CASES` | Case count for the ASCII validator fuzz test.  The default is 50. |

## First Build

Install the runtime tools, build the compiler, build the native ABI runner, and run the execution suite from the repository root.  The download command writes only under the ignored `build` directory.  The suite rebuilds the compiler before running its Node drivers.

```sh
tools/download-wasmtime.sh
lake build
tools/build-wasmtime-host.sh
node test/run_all.js
```

Initialize the proof workspace separately.  The first `lake build Project` fetches pinned dependencies and may compile thousands of Lean jobs, while later builds reuse `.lake` outputs.  Building the verifier is required only for an intentional `--update` of a checked-in artifact.

```sh
cd proofs/talos-gcd/lean
lake build Project

cd .lake/packages/CodeLib/verifier
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
| Artifact proof | The per-case Talos script, `lake build Project` in the proof workspace, and the execution test for the source entry. |
| Toolchain or artifact-producing tool | Full execution and proof gates, artifact-byte review, version and checksum documentation, and trusted-base review. |

`node test/run_all.js` is the full execution gate.  It covers report classification, ownership reports, Wasmtime-only execution, core semantics, reference counting, allocation, ASCII strings, integer maps, JSON, WASI adapters, self-emission, standard Lean comparisons, IR comparisons, and fuzz cases.  `tools/check-wat.sh` checks that parsing compiler-emitted WAT produces the same bytes as direct binary emission.

## Proof Artifacts

The proof workspace contains fifteen checked artifacts.  `proofs/talos-gcd/rust/build/<case>/program.wasm` and `program.wat` are checked-in proof inputs, `Project/<Case>/Program.lean` is generated by the Talos verifier emitter, and `Project/<Case>/Spec.lean` is handwritten.  Never edit a generated `Program.lean` file.

A normal per-case check recompiles the Lean entry, regenerates temporary WASM and WAT, compares both files with the checked-in inputs, and builds the handwritten proof.  Run the aggregate script after any compiler change because a shared backend or runtime change can affect every artifact.  A byte mismatch is a failed gate until its cause is understood.

```sh
tools/check-talos-clob-cancel.sh
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
| A proof build is unexpectedly large | Confirm that the command is running under `proofs/talos-gcd/lean` with Lean 4.31.0.  A cold dependency build compiles thousands of jobs. |
| A generated model builds but a theorem fails | Treat the new instruction stream as the proof subject and repair `Spec.lean`; do not edit `Program.lean`. |

Failure messages should identify the command, module, entry, declaration, and rejected construct whenever those values exist.  Repository commands reserve stdout for requested reports and artifacts and stderr for failures.  The CLI does not yet apply one exit-status scheme to every command, so tests that depend on a status must assert the implemented command behavior.

## Documentation Maintenance

Each document has one role.  The repository overview provides setup and a user-facing introduction; this guide owns development workflow and gates; the manual owns source patterns and diagnostics; the specification owns semantics and rejection boundaries; the Talos README owns the current proof inventory; the verification guide owns proof procedure; the development plan owns future work; and the journal owns history and rationale.  The technical summary explains architecture without serving as a second roadmap.

Update the authoritative document in the same change as the behavior it describes.  Keep volatile counts in one inventory and link to it elsewhere when the number adds no value.  Mark historical experiments and superseded plans at the top so a reader cannot mistake them for current procedure.
