# Demo 1 artifact-proof benchmark

This directory preserves ten complete proof packages measured on 2026-08-05.  Every package binds the same request and the same 1,938-byte WASM module with SHA-256 digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  The retained runs cover the initial proof kit and three-run series for word-address lemmas, the complete fixed-array allocator theorem, and the complete singleton-array result theorem.

## Results

| Variant | Runs | Stage-5 median | Range |
|---|---:|---:|---:|
| Initial proof kit | 1 | 3,516.775 s | 0.000 s |
| Word-address lemmas | 3 | 1,964.130 s | 1,889.300 s |
| Fixed-array allocator | 3 | 1,134.008 s | 1,615.319 s |
| Fixed-array singleton result | 3 | 489.993 s | 243.993 s |

The fixed-array allocator median is 830.122 seconds, or 42.3 percent, below the word-address median.  Its individual times are 2,556.812, 1,134.008, and 941.494 seconds.  Each accepted proof imports `Project.ProofKit.FixedArrayAllocator` and applies `region_spec` to the exact emitted allocator suffix.

The fixed-array singleton median is 489.993 seconds, which is 644.015 seconds, or 56.8 percent, below the allocator median.  Its individual times are 680.396, 436.403, and 489.993 seconds.  Each accepted proof imports `Project.ProofKit.FixedArraySingleton` and applies `region_result_spec` to the exact combined allocator and result suffix.

The large earlier ranges come from Codex search rather than outer acceptance.  The singleton Codex intervals are 637.892, 394.336, and 447.849 seconds, while their outer-acceptance intervals are 32.874, 35.225, and 35.312 seconds.  The combined theorem reduced both the median and range, though three observations do not establish the complete timing distribution.

## Measurement and controls

The performance metric is wall-clock time from the Stage 5 heading to the first proof accepted by the independent outer check.  `benchmark.json` records the frozen files, semantic tool pins, resource profile, cache policy, accepted proof digest, and measured interval for each run.  The benchmark checker validates every retained package before computing variant medians and ranges.

The packages record Codex CLI version `0.146.0`, but the first two historical packages did not record the Codex model or reasoning setting.  The checker reports that limitation on every comparison.  Proof packages generated after telemetry was added contain `proof-telemetry.json`, which separates Codex-session time and outer-acceptance time while retaining the Stage 5 total as the authoritative metric.

The telemetry schema does not record individual Codex Lean commands.  Command-level attribution requires a stable event protocol or a traced runner that preserves the repository execution boundary.  The present evidence therefore establishes the end-to-end timing change and locates its variance in the Codex interval, but it does not count failed Lean checks or assign time to individual proof obligations.

## Commands

The read-only checker validates every retained package and frozen identity in `benchmark.json`.  The comparison command validates a new proof package and reads its Stage 5 telemetry without running Lean or Codex.  Both commands accept an optional benchmark directory.

```text
tools/leanexegen-benchmark check
tools/leanexegen-benchmark compare <proof-package>
```

The benchmark subcommand reproves the `timing-2` package, validates the frozen identity, and invokes package verification after Stage 5 timing has stopped.  It creates the requested WASM file and adjacent proof package, and it refuses an output path that already exists.  All Lean work remains under the `tools/leanexegen` and `tools/leanrun` execution boundary.

```text
tools/leanexegen benchmark -o /tmp/demo1-measured.wasm
```
