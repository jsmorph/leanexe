# Native WASI task

Keep this file current at each checkpoint; commit and push it with the work.

## Goal and branch

Finish the native WASI Preview 1 API on `wasi`, based on `main` at
`a4655383`, independently of `io`. All 46 Preview 1 functions are exposed
through `LeanExe.Wasi.Action` and the `compile-wasi-api` command.

## Completed

- API definitions, compiler lowering, and WASI host wrappers.
- Sequencing of effects, including ignored results and repeated actions.
- Returned child ownership, shared buffers, local array transfers, and
  reclamation across streaming iterations.
- Runtime coverage for arguments/environment, clocks, files, polling,
  binary streaming, errors, and live TCP through an inherited socket.
- Reconciled native-mode documentation across the manual, specification,
  compiler guide, and documentation index.
- Independent verification of the other session's implementation commit
  `0c5af023`; verification notes published in `1d6e1f6b`.

## Current checkpoint

The ownership fix changed scalar-loop output even where there are no owned
accumulators. The GCD output consequently differs from its checked-in proof
model. A compatibility change in `LeanExe/Wasm/Binary.lean` preserves the old
scalar encoding while retaining snapshots for loops that reclaim owners.
The compiler and both image test modules build with this change.

Checks repeated after that change:

- 38 native WASI cases passed, including streaming and socket exchange.
- 41 reference-count cases passed; seven allocation-accounting assertions
  passed (six leak-free cases and one deliberately retaining blocks).
- All 13 WAT/binary comparisons passed.
- Core correctness: 812 accepted cases, 48 rejections, and 14 expected traps.

Additional checks passed before this last emitter change:

- Self-emitted LEB128: 75 cases.
- Matcher extraction: four IR cases and one WAT scan.
- Legacy WASI driver: 33 runtime cases, two traps, nine rejections, and
  sixteen compile checks.

## Remaining work and known blockers

1. Resolve the remaining GCD proof-model difference: extraction adds two
   locals and result copies. A clean build of the unchanged `main` base is
   underway to determine whether this difference predates `wasi`.
2. Finish `tools/talos-proof.js check --all`. This has **not passed yet**.
   The pinned verifier now builds and generates models. The local compiler
   override supplies the pinned toolchain's standard include/link flags and
   disables C optimization only for the generated WAT parser. Bulk Mathlib
   cache download was stopped; updates use `MATHLIB_NO_CACHE_ON_UPDATE=1`.
   The aggregate attempt was stopped during proof-source dependency setup
   to finish the baseline comparison first. The tracked GCD cache remains
   unchanged; its temporary regenerated candidate is retained under `build/`.
3. Complete the final audit, update this status, and publish a clean branch.

The aggregate `test/run_all.js` currently stops at a historical release-input
identity mismatch. The documentation gate rejects an absolute workspace path
in `paper/wgsl-verification-report/review.md`. Both failures were reproduced
on the unchanged `main` base `a4655383`; historical records were left intact.
The CLI error driver passes all nine diagnostic cases, then its help-output
assertion fails because the authorized local runner writes a warning to stderr.

## Reproduction notes

This checkout uses Lean 4.34.0-rc2, Node 24.13.0, wasm-tools 1.251.0, and
Wasmtime 44. Every Lean/Lake invocation goes through `tools/leanrun` with
the user's authorized `LEANRUN_LOCAL=1`; do not run Lean concurrently.
Local tool paths are in the ignored `build/wasi-env.sh`. Test/build logs are
under `build/`; generated modules and comparisons are under `tmp/`.
`LEANRUN_LOCKDIR` points into the shared workspace because command sessions
can have separate `/tmp` directories. Run compiler/proof drivers sequentially.
