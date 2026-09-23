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

## Current checkpoint: implementation ready for review

The ownership fix changed scalar-loop output even where there are no owned
accumulators. A compatibility change in `LeanExe/Wasm/Binary.lean` preserves the old
scalar encoding while retaining snapshots for loops that reclaim owners.
The compiler and both image test modules build with this change.

A clean compiler build of the unchanged base `a4655383` and this branch now
produce identical 1,257-byte GCD modules (SHA-256
`202034399188f494471d91426c957a986ffd7ff74d9f72fde330bf47a5daab71`).
The remaining difference from the tracked proof model therefore predates
`wasi`. No proof model was changed.

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

## Next steps and gate limitations

1. Review the native WASI implementation and ownership changes on `wasi`.
2. Resolve the inherited verification-record problems separately, then rerun
   the full execution, documentation, and source-proof gates. These gates
   **have not passed**; the successful targeted checks above are narrower.

The pinned Talos verifier builds and generates models. The focused
`tools/talos-proof.js check gcd` fails because the tracked model is stale,
including extra locals and result copies emitted by the unchanged base.
The final `check --all` attempt was stopped during cold proof-source
dependency setup after this inherited blocker was established. The tracked
GCD cache remains unchanged; its generated candidate is under `build/`.
The local verifier compiler override supplies the pinned toolchain's
standard include/link flags and disables C optimization only for the
generated WAT parser. Updates use `MATHLIB_NO_CACHE_ON_UPDATE=1`.

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
