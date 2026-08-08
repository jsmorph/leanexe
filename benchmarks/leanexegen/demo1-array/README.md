# Demo 1 artifact-proof benchmark

This directory preserves fourteen complete proof packages measured on 2026-08-05 and 2026-08-08.  Every package binds the same request and the same 1,938-byte WASM module with SHA-256 digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  The retained runs cover the initial proof kit, three-run series for word-address lemmas, the complete fixed-array allocator theorem, the complete singleton-array result theorem, the first complete annotation comparison, and the isolated scalar-descriptor comparison.

## Results

| Variant | Runs | Stage-5 median | Range |
|---|---:|---:|---:|
| Initial proof kit | 1 | 3,516.775 s | 0.000 s |
| Word-address lemmas | 3 | 1,964.130 s | 1,889.300 s |
| Fixed-array allocator | 3 | 1,134.008 s | 1,615.319 s |
| Fixed-array singleton result | 3 | 489.993 s | 243.993 s |
| Codex 0.147.0 scalar baseline | 1 | 2,017.931 s | 0.000 s |
| Codex 0.147.0 full annotations with scalar descriptor | 1 | 3,692.913 s | 0.000 s |
| Codex 0.147.0 calls-only scalar control | 1 | 2,645.818 s | 0.000 s |
| Codex 0.147.0 isolated scalar descriptor | 1 | 3,894.697 s | 0.000 s |

The fixed-array allocator median is 830.122 seconds, or 42.3 percent, below the word-address median.  Its individual times are 2,556.812, 1,134.008, and 941.494 seconds.  Each accepted proof imports `Project.ProofKit.FixedArrayAllocator` and applies `region_spec` to the exact emitted allocator suffix.

The fixed-array singleton median is 489.993 seconds, which is 644.015 seconds, or 56.8 percent, below the allocator median.  Its individual times are 680.396, 436.403, and 489.993 seconds.  Each accepted proof imports `Project.ProofKit.FixedArraySingleton` and applies `region_result_spec` to the exact combined allocator and result suffix.

The large earlier ranges come from Codex search rather than outer acceptance.  The singleton Codex intervals are 637.892, 394.336, and 447.849 seconds, while their outer-acceptance intervals are 32.874, 35.225, and 35.312 seconds.  The combined theorem reduced both the median and range, though three observations do not establish the complete timing distribution.

The first annotated run increased Stage 5 by 1,674.982 seconds, or 83.0 percent, from the 2,017.931-second unannotated baseline.  Codex time increased from 1,953.883 to 3,565.493 seconds, while outer acceptance increased from 57.008 to 112.292 seconds.  The package combined the scalar descriptor with length-dispatch and direct-call recipes, and its journal records substantial work on the wrapper recipe as well as descriptor evaluation, so this pair measures the complete annotation package rather than the scalar theorem alone.

The isolated comparison retains the same two direct-call recipes in both packages and adds only `function-0.while-loop-0` to the candidate.  The candidate took 3,894.697 seconds, compared with 2,645.818 seconds for the control, an increase of 1,248.879 seconds, or 47.202 percent.  Codex time increased by 48.966 percent, while outer acceptance fell by 3.079 percent, and independent verification accepted both packages.

The annotated proof has 674 lines and 3,257 whitespace-delimited words, compared with 722 lines and 3,418 words in the control.  Lines fell by 6.648 percent and words fell by 4.710 percent, providing secondary evidence that the checked descriptor and shared loop theorem reduce local proof structure.  Raw byte length increased because the candidate repeatedly uses long generated and qualified declaration names; identifier spelling does not count against the proof, but the proving-time regression still rejects this version of the scalar descriptor as a promoted recipe.

The control journal records that Codex reconstructed the neutral scalar descriptor and reached its semantic cases during its first few edited checks.  The candidate used the generated descriptor equality and `ScalarTransition.whileProgram_spec`, but did not use `Stmt.eval_preserves_below`; both runs spent most of their work on the trial-division invariant, scalar evaluator cases, fixed-width arithmetic, and public array wrapper.  The next scalar experiment will use checked application-local transition equations that hide scratch state and a shared wrapper composition that removes unrelated entry-proof variance.

The shared wrapper composition now has a checked implementation, but no timing observation appears in this table yet.  Its generic theorem treats the scalar callee as a parameter and covers the complete singleton-array entry function, while the generated Demo 1 equality identifies the frozen entry program with that template by `rfl`.  The next matched run will provide this same wrapper composition to both scalar configurations so the comparison continues to isolate the scalar-transition assistance.

## Measurement and controls

The primary performance metric is elapsed time from the Stage 5 heading to the first proof accepted by the independent outer check, measured through `process.hrtime.bigint`.  Accepted proof lines, syntax volume, local scaffolding, and shared theorem applications provide secondary structural evidence; raw source bytes identify content but do not measure proof complexity.  `benchmark.json` records and checks the ten Codex 0.146.0 packages, while the four scalar directories retain the Codex 0.147.0 packages with schema-two task identities and complete telemetry.

The host wall clock changed during both isolated runs.  The calls-only control's UTC timestamps span about two hours while its monotonic total is 2,645.818 seconds, and the scalar candidate's timestamps span nearly four hours while its monotonic total is 3,894.697 seconds.  The comparison therefore uses `totalMilliseconds`, `codexSessionMilliseconds`, and `outerAcceptanceMilliseconds`, rather than subtracting the recorded UTC timestamps.

The historical packages record Codex CLI version `0.146.0`, while the scalar comparison records artifact-proof CLI version `0.147.0` and preserves the earlier task identities under stage-report schema two.  The first two historical packages did not record the Codex model or reasoning setting, and the checker reports that limitation on every comparison.  Proof packages generated after telemetry was added contain `proof-telemetry.json`, which separates Codex-session time and outer-acceptance time while retaining the Stage 5 total as the authoritative metric.

The telemetry schema does not record individual Codex Lean commands.  Command-level attribution requires a stable event protocol or a traced runner that preserves the repository execution boundary.  The present evidence therefore establishes the end-to-end timing change and locates its variance in the Codex interval, but it does not count failed Lean checks or assign time to individual proof obligations.

## Commands

The read-only checker validates every package and frozen identity listed in `benchmark.json`.  The comparison command validates a compatible Codex 0.146.0 proof package and reads its Stage 5 telemetry without running Lean or Codex.  The scalar packages use Codex 0.147.0 and remain directly verifiable with `tools/leanexegen verify` until the benchmark manifest supports multiple Codex series.

```text
tools/leanexegen-benchmark check
tools/leanexegen-benchmark compare <proof-package>
```

The benchmark subcommand reproves the `timing-2` package, validates the frozen identity, and invokes package verification after Stage 5 timing has stopped.  It creates the requested WASM file and adjacent proof package, and it refuses an output path that already exists.  All Lean work remains under the `tools/leanexegen` and `tools/leanrun` execution boundary.

```text
tools/leanexegen benchmark -o /tmp/demo1-measured.wasm
```
