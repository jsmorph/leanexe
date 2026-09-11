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
node tools/euler-block-run.mjs run 192 tmp/riemann-blocks-192
node tools/euler-block-run.mjs run 800 tmp/riemann-blocks-800
node tools/euler-riemann-large.mjs write tmp/riemann-blocks-800/run.ndjson data/euler-riemann-800-v1
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
comparison.  The successful benchmark and both 800-grid jobs use that
immutable source and the tools installed in the first snapshot.

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
| `leanexe-riemann-800-20260911-1` | 4G high, 6G max, 100% CPU, 21,600 seconds | Final status 143: stopped after the user authorized the process design |
| `leanexe-riemann-800-check-20260911-1` | 4G high, 6G max, 100% CPU, 28,800 seconds | Final status 143: predecessor failed, so verification did not start |

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
The user superseded the serial execution design with 24 concurrent WASM
processes.  The serial job was stopped with its partial output preserved.
Its final status is 143, and the waiting checker returned the same status
without starting verification.  The last serial progress line records
step 800, time 0.19010000848955011, and zero retries.

The preserved partial serial record is
`/mnt/vq/leanexe-riemann-20260911-libm/tmp/euler-2d-run-9lAWkE/run.ndjson`.
Its sibling `stderr.log` records progress every 50 steps.  The final
compressed-data check, retrieval, figures, and article remain pending.

The check service waited through `leanrun-job wait`, whose nonzero result
prevented the large-run driver's `check` command from starting.
Both services together declared 8G memory high, 12G maximum, 200% CPU,
and 1,024 tasks, within the aggregate limits.  The first check submission
returned SSH status 255 without a diagnostic and created no job.  The
retry succeeded through the approved helper.  Each service retains its
own final status and log.

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

## Twenty-four WASM processes

The [Bash sweep](../tools/euler-block-wave.sh) starts 24 workers with `&`
and waits for every PID.  Worker b owns rows floor(nb/24) through
floor(n(b+1)/24) minus one.  The [WASM worker](../tools/euler-block-worker.wat)
performs initialization checks, speed scans, cell updates, and boundary
flux calls using the three unchanged numerical artifacts.  The
[C host](../tools/euler-block-host.c) loads Wasmtime modules and transfers
files.  Each process has its own store and memory.

The [coordinator](../tools/euler-block-run.mjs) first waits for the speed
scan and selects a global timestep.  Every x worker reads the previous
accepted state.  After all x workers exit successfully, every y worker
reads the completed x files and the adjacent block's boundary row.  The
physical boundary copies its nearest interior row.  A rejected block
causes a global retry at half the timestep.  Input files remain immutable,
and every attempted sweep has a fresh output directory.

Block files contain little-endian binary64 conserved quantities in cell
order.  Accepted y files also contain pressure.  Omitting unused pressure
from x files reduces retained cell data to 46.08 MB per 800-grid timestep.
About 3,370 steps therefore require 155.3 GB of cell data, plus file-system
metadata and raw records.  All intermediate files remain available.

The Wasmtime 44 C API converts the worker WAT and compiles the four
modules once per source/host build.  Subsequent processes load those local
compiled modules.  The build receipt identifies source, frozen kernel
bytes, flags, architecture, host executable, worker WASM, and compiled
modules.  The execution receipt binds the raw record hash, coordinator
sources, Node version, and physical call counts.  Dataset packaging and
checking verify that raw-record binding.  The batch-WASM orchestration
has executable tests.  The existing exact-byte theorems cover the three
numerical kernels.

The 26-grid test uses unequal block sizes and runs through time 0.8 in
110 steps without retries.  Its complete NDJSON record matches the serial
run byte for byte.  Independent replay, compressed-data checking,
execution-metadata preservation, forced rejection, and missing-input
failure tests pass.  The latest local evidence is
`tmp/euler-block-test-KBfesv`, with a measured process-run time of
9.206926213 seconds under the standard one-CPU runner.  Dev timing and
the full 800-grid result remain pending.

The [dev command script](../tools/euler-riemann-dev.sh) owns SSH access,
persistent submission, tool paths, limits, benchmark comparison, the
800-grid run, packaging, and verification.  Its local commands are
`tools/euler-riemann-dev.sh start benchmark`, then
`tools/euler-riemann-dev.sh start run`.  The same script accepts `status`,
`log`, and `result` for either phase.  The run requires a successful
benchmark.  Each phase requires an idle persistent-job slice before
claiming its 24-CPU quota.  Both use 16G memory high, 20G maximum, zero
swap, and 1,024 tasks.  The fresh project directory is
`/mnt/vq/leanexe-riemann-20260911-blocks-script`.
