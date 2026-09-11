# Additional 800-grid Riemann calculation

This record expands phase 11 of the [development plan](../plan.md).  The
user authorized the additional run on 2026-09-11, using `ssh dev` and its
available capacity.  The 192 × 192 [published experiment](../data/euler-riemann-v1/README.md)
retains its numerical data and figures.

## Method and output

The 800 × 800 case uses the same four primitive states, initial interfaces
at x = y = 0.8, unit-square domain, final time 0.8, gamma 1.4, first-order
Rusanov flux, x-then-y splitting, transmissive boundaries, and CFL settings.
The three proved WASM artifacts are unchanged.  The native host accepts
meshes through 800 and writes a progress record every 50 steps.

The [large-run driver](../tools/euler-riemann-large.mjs) reads one JSON event
at a time, verifies the complete numerical recurrence, and retains the
latest density/pressure frame.  It preserves the native NDJSON record and
emits ordered gzip parts with at most 64 MiB of uncompressed events per
part, a compressed cell CSV, the timestep CSV, and a summary.  The reader
rejects any event exceeding 64 MiB before JSON parsing.  This bound covers
the final 800-grid conservative-state record.

Node's [stream pipeline](https://nodejs.org/download/release/v24.13.0/docs/api/stream.html#streampipelinesource-transforms-destination-options)
propagates read, compression, and write errors.  The
[gzip reader](https://nodejs.org/download/release/v24.13.0/docs/api/zlib.html#class-zlibgunzip)
accepts the concatenated parts.  Splitting raw records and compressing the
cell CSV keeps individual publication files below GitHub's
[100 MiB limit](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github).
The summary records part order, content hashes, source hashes, method,
initial states, numerical diagnostics, and measured phase times.

Within an admitted persistent dev job, the driver commands are:

```text
node tools/euler-riemann-large.mjs run 192 tmp/riemann-dev-192
node tools/euler-riemann-large.mjs run 800 data/euler-riemann-800-v1
node tools/euler-riemann-large.mjs check data/euler-riemann-800-v1
```

The job selects the pinned Node executable and Wasmtime C API.  Each run
requires a fresh output directory.  `write run.ndjson directory` verifies
an existing native record and produces the same output format.  The
[plot script](../tools/euler-riemann-plot.py) accepts either plain or
gzip-compressed cell CSV.

## Host preparation

| Item | Checked value |
|------|---------------|
| SSH helper | `/home/somebody/src/vq/tools/dev-ssh dev` |
| AWS instance | `i-0837c0234cb65b764`, running, `c8i.8xlarge`, x86-64 |
| Data volume | `vol-05f3783d7690242c8`, writable ext4 at `/mnt/vq`, 170 GiB free |
| Persistent user manager | Linger enabled |
| Aggregate limits | 48 GiB high, 52 GiB maximum, zero swap, 24 CPUs, 2,048 tasks |
| Active persistent jobs at inspection | None |
| Runner commit | `297b46c55bfc127dad5b5bbc680fc28a1c3665e3` |
| Fresh runner directory | `/mnt/vq/leanrunner-release-20260911-297b46c-leanexe` |
| Runner tests | Local and remote shell syntax, executable modes, and empty checksum comparison pass |
| Source snapshot | `/mnt/vq/leanexe-riemann-20260911-stream` |
| Source revision | `76f874f660dd7e08d9d62d27470be12362b0cd4e` |
| Source transfer | 6,777 tracked files, 98,282,441 bytes, empty checksum comparison |
| Available Lean toolchain | `/mnt/vq/elan/toolchains/leanprover--lean4---v4.34.0-rc2` |

The user approved installation of Node 24.13.0 and the Wasmtime 44.0.0
C API.  Both x86-64 archives passed their pinned SHA-256 checks and were
extracted under the snapshot's `build/tools` directory.  Node reports
24.13.0.  The host compiler is GCC 11.5.0.

The first benchmark, `leanexe-riemann-192-20260911-1`, returned final status
1 during linking: the C host omitted `-lm`, leaving `fmin` unresolved.
The host build now links the system math library after the source input,
following GCC's [library-order rules](https://gcc.gnu.org/onlinedocs/gcc/Link-Options.html).
The build receipt includes the library options.  The failed snapshot and
job record remain preserved.  Corrected revision
`c64507bf0a0729cbab03cd1aee416471a74f222e` was copied to
`/mnt/vq/leanexe-riemann-20260911-libm` and passed an empty checksum
comparison.  Both runs below use that immutable source and the tools
installed in the first snapshot.

The current leanrunner skill and its complete dev runbook govern source
synchronization, checksum comparison, resource admission, persistent
submission, and final-status retrieval.  The older repository
`tools/leanrun-dev` uses superseded remote paths.  Existing remote project
and runner directories remain preserved.

## Dev execution

| Job | Limits | Result |
|-----|--------|--------|
| `leanexe-riemann-192-20260911-1` | 4G high, 6G max, 100% CPU, 1,800 seconds | Final status 1: missing math-library linkage |
| `leanexe-riemann-192-20260911-2` | 4G high, 6G max, 100% CPU, 1,800 seconds | Final status 0: native run and independent replay pass |
| `leanexe-riemann-800-20260911-1` | 4G high, 6G max, 100% CPU, 21,600 seconds | Started 2026-09-11 at 17:44:58 UTC.  Final result pending |

Every job uses zero swap and a 512-task ceiling.  The successful benchmark
ran from 17:41:02 to 17:44:02 UTC.  Native execution including compilation
took 131.18569411 seconds.  Independent replay took 44.491457276 seconds.
All 808 steps passed, with zero retries.  Its complete numerical result,
decompressed cell CSV, and timestep CSV match the published 192-grid data
exactly.  Local copies of both benchmark job records and the new 192-grid
dataset passed checksum comparisons after retrieval.

Scaling computation by `(800/192)^3` estimates 2.64 hours of native
execution and 0.89 hours of replay, plus a comparable second replay for
the packaged-data check.  These are estimates from the 192-grid timing.
The approved serial calculation is running.  Parallel execution would
require a separate host implementation with independent Wasmtime stores
and further tests.

The active native record is
`/mnt/vq/leanexe-riemann-20260911-libm/tmp/euler-2d-run-9lAWkE/run.ndjson`.
Its sibling `stderr.log` records progress every 50 steps.  The driver will
write `data/euler-riemann-800-v1` only after its independent replay passes.
The final compressed-data check, retrieval, figures, and article remain
pending.

The [comparison plot script](../tools/euler-riemann-compare.py) places two
resolutions on shared density and pressure scales with identical contour
levels.  It passed a render test using the existing 8-grid and 192-grid
datasets, and its PNG was inspected.  Final comparison figures await the
800-grid data.

## Completed local tests

The native, in-memory, and streamed runtime tests pass for the three
8-grid scenarios.  Both readers reject eight corrupted records, propagate
input errors, and reject oversized events.  An 8-grid, 21-frame Riemann
dataset passes write and compressed replay.  A two-part gzip fixture
passes the same replay and CSV comparison.

The streamed replay of the completed 192-grid native record passes all
808 steps in 34.8217 seconds under the standard workstation runner.
Its decompressed cell CSV, timestep CSV, raw event bytes, and every result
field match the published experiment.  Rendering the compressed cell CSV
reproduces the published PNG, SVG, and PDF byte for byte.  These tests
establish the new record path's agreement with the existing result.  The
verifier also requires the last snapshot to have the final time, because
the cell CSV takes its pressure values from that snapshot.
