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
| Available Lean toolchain | `/mnt/vq/elan/toolchains/leanprover--lean4---v4.34.0-rc2` |

Dev's system Node is 18.20.8.  The required Node 24.13.0 and Wasmtime
44.0.0 C API need installation in the project tools directory.  Approval
was requested under the user's missing-tool instruction.  A project
snapshot, remote 192-grid timing, and 800-grid run remain pending.

The current leanrunner skill and its complete dev runbook govern source
synchronization, checksum comparison, resource admission, persistent
submission, and final-status retrieval.  The older repository
`tools/leanrun-dev` uses superseded remote paths.  Existing remote project
and runner directories remain preserved.

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
