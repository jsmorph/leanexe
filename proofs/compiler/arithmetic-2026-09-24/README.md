# Arithmetic milestone evidence

Candidate: `878cfd1e` on `correct`. Lean: 4.34.0-rc2, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Node: 24.13.0. Platform:
macOS arm64, explicitly authorized local `tools/leanrun` execution with one
Lean thread and the shared machine lock. No separate checkout or deliberately
broken-copy checks are required, following the user's current instructions.

| Check | Command | Result |
| --- | --- | --- |
| General arithmetic theorem | `tools/arithmetic-check.js proof` | Exit 0; build completed, all nine axiom audits passed |
| Production compiler and execution | `tools/arithmetic-check.js engine` | Exit 0; admission/reserved-name checks and 85 comparisons across seven declarations passed |
| Independent type safety | `tools/type-safety.js check` | Exit 0; core build, 19 behavior-test files and 438 theorem audits passed |
| Standalone source package | Bundled verifier on the extracted archive | Pending at this checkpoint |

The proof build started at `efd91d88`; its Lean inputs are identical at
`878cfd1e`. Its completed audit used the auditor committed at `878cfd1e`.
The compiler execution and type-safety checks used `878cfd1e`.

The original checkout used the environment from `tools/macos-env.sh`, with its
pinned local installation under `build/tools`. The `LEANRUN_LOCAL=1` and
`LEANRUN_INHERIT_PRIORITY=1` settings were explicitly authorized for this Mac.
All builds used `tools/leanrun` with bounded timeouts, never concurrent Lean.
No type-safety axiom rule or semantic claim was weakened.

The retained `proof.log`, `axioms.log`, `type-safety.log`, `execution.log`, native
`expected.jsonl` and seven emitted `.wasm` modules record the passing checks.
`arithmetic-proof.tar.gz` is the source-only package from `878cfd1e` with 133 Lean
modules and all required pinned configuration and verification tools.

Archive SHA-256:
`ca502069636102311a70ba0276303261388008ccf0e6c468ad9ba540d2c15105`.
The archive inventory records the full originating commit and tree. Its hash
above establishes package identity; the inventory alone is not a signature.
