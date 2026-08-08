# Demo 1 artifact-proof benchmark

This directory preserves twenty complete proof packages measured on 2026-08-05 and 2026-08-08.  Every package binds the same request and the same 1,938-byte WASM module with SHA-256 digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  The retained runs cover the initial proof kit, three-run series for word-address lemmas, the complete fixed-array allocator theorem, the complete singleton-array result theorem, the first complete annotation comparison, the isolated scalar-descriptor comparison, the matched compact-transition comparison, the checked scalar-entry distribution, and the stronger `TerminatesWith` screen.

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
| Codex 0.147.0 shared-wrapper transition control | 1 | 2,262.084 s | 0.000 s |
| Codex 0.147.0 checked compact transitions | 1 | 1,965.454 s | 0.000 s |
| Codex 0.147.0 checked scalar entry | 3 | 1,421.556 s | 318.935 s |
| Codex 0.147.0 stronger `TerminatesWith` adapter | 1 | 1,418.100 s | 0.000 s |

The fixed-array allocator median is 830.122 seconds, or 42.3 percent, below the word-address median.  Its individual times are 2,556.812, 1,134.008, and 941.494 seconds.  Each accepted proof imports `Project.ProofKit.FixedArrayAllocator` and applies `region_spec` to the exact emitted allocator suffix.

The fixed-array singleton median is 489.993 seconds, which is 644.015 seconds, or 56.8 percent, below the allocator median.  Its individual times are 680.396, 436.403, and 489.993 seconds.  Each accepted proof imports `Project.ProofKit.FixedArraySingleton` and applies `region_result_spec` to the exact combined allocator and result suffix.

The large earlier ranges come from Codex search rather than outer acceptance.  The singleton Codex intervals are 637.892, 394.336, and 447.849 seconds, while their outer-acceptance intervals are 32.874, 35.225, and 35.312 seconds.  The combined theorem reduced both the median and range, though three observations do not establish the complete timing distribution.

The first annotated run increased Stage 5 by 1,674.982 seconds, or 83.0 percent, from the 2,017.931-second unannotated baseline.  Codex time increased from 1,953.883 to 3,565.493 seconds, while outer acceptance increased from 57.008 to 112.292 seconds.  The package combined the scalar descriptor with length-dispatch and direct-call recipes, and its journal records substantial work on the wrapper recipe as well as descriptor evaluation, so this pair measures the complete annotation package rather than the scalar theorem alone.

The isolated comparison retains the same two direct-call recipes in both packages and adds only `function-0.while-loop-0` to the candidate.  The candidate took 3,894.697 seconds, compared with 2,645.818 seconds for the control, an increase of 1,248.879 seconds, or 47.202 percent.  Codex time increased by 48.966 percent, while outer acceptance fell by 3.079 percent, and independent verification accepted both packages.

The annotated proof has 674 lines and 3,257 whitespace-delimited words, compared with 722 lines and 3,418 words in the control.  Lines fell by 6.648 percent and words fell by 4.710 percent, providing secondary evidence that the checked descriptor and shared loop theorem reduce local proof structure.  Raw byte length increased because the candidate repeatedly uses long generated and qualified declaration names; identifier spelling does not count against the proof, but the proving-time regression still rejects this version of the scalar descriptor as a promoted recipe.

The control journal records that Codex reconstructed the neutral scalar descriptor and reached its semantic cases during its first few edited checks.  The candidate used the generated descriptor equality and `ScalarTransition.whileProgram_spec`, but did not use `Stmt.eval_preserves_below`; both runs spent most of their work on the trial-division invariant, scalar evaluator cases, fixed-width arithmetic, and public array wrapper.  Those observations led to checked fixed-frame transition equations that summarize scratch staging and a shared wrapper composition that removes unrelated entry-proof variance.

The matched transition comparison gives both packages the same length-dispatch and direct-call recipes and the same complete singleton-wrapper composition.  The candidate adds only `function-0.while-loop-0`, whose generated declarations include checked condition and body transition equations.  Both packages preserve the same artifact, proof-kit identity, tool pins, formal specification, source, Codex identity, and task settings, and independent verification accepts both.

The checked-transition candidate completed Stage 5 in 1,965.454 seconds, compared with 2,262.084 seconds for the control.  The reduction is 296.630 seconds, or 13.113 percent; Codex-session time fell by 323.088 seconds, or 14.945 percent, while outer acceptance took 26.755 seconds longer.  This one matched observation promotes the compact transition equations for further testing but does not establish their timing distribution.

The candidate proof has 635 lines and 12 `wp_run` applications, while the control has 643 lines and 36 `wp_run` applications.  The candidate instead rewrites with the generated condition equation three times and the generated body equation five times.  These counts show that the annotation removed repeated instruction-level symbolic execution; declaration spelling, identifier length, and raw source bytes have no negative weight.

Both journals identify the function-entry frame as the next general boundary.  The candidate still spent several checks converting `Function.toLocals` into the generated `U64State` before `whileProgram_spec` applied, while the control also derived entry argument order and fixed-store quantification.  A generated, checked entry-to-loop adapter should address this repeated work before the transition method moves to a held-out scalar artifact.

The checked scalar-entry series gives all three sessions the same wrapper composition, scalar descriptor, compact transition equations, and generated entry-to-loop `wp` equivalence.  The runs completed Stage 5 in 1,282.711, 1,601.646, and 1,421.556 seconds, producing a 1,421.556-second median and a 318.935-second range.  The median is 543.898 seconds, or 27.7 percent, below the matched compact-transition result, while median Codex time fell by 493.507 seconds and median outer acceptance fell by 47.876 seconds.

The three accepted proofs contain 548, 596, and 572 lines and use 9, 10, and 12 `wp_run` applications.  Their medians reduce the matched proof from 635 to 572 lines and from 12 to 10 `wp_run` applications.  Every proof uses the generated entry equality once, the checked loop theorem once, and the compact transition equations; their application-level prime-factor arguments differ, so the result does not depend on retrieval of one proof structure.

All three journals record discovery of the same WebAssembly operand-stack reversal before the lower-level entry equality applies.  The annotation generator now emits a stronger `terminates_with_of_loop` theorem whose conclusion states the external stack order and whose premise starts at the checked loop-head state.  A current-input annotation build and separate package verification accept that theorem against the same frozen artifact.

The second journal also records a lengthy reconstruction of `(fuel - 1).toNat = fuel.toNat - 1`, while the first and third proofs use `UInt64.toNat_sub_of_le`.  The selected arithmetic guidance now names that theorem, the corresponding `Project.ProofKit.Memory` theorem, and the required conversion from `UInt64` order to natural-number order.  These changes will receive a new fixed-artifact timing screen before a held-out scalar loop.

The stronger-adapter screen completed Stage 5 in 1,418.100 seconds, 3.456 seconds below the preceding three-run median.  Codex took 1,326.745 seconds and outer acceptance took 79.367 seconds, so the total remains inside the observed entry-series range and supplies no evidence of a proving-time reduction.  The accepted proof fell from the prior medians of 572 lines and 10 `wp_run` applications to 541 lines and five applications, while applying the stronger adapter once and the checked condition and body equations two and four times.

The journal records direct selection of the stronger adapter, the complete singleton wrapper, and the compact transition equations.  It then spends its revisions on the application invariant, natural-number facts about prime factors, and conversions between `UInt64` arithmetic and natural arithmetic; the supplied subtraction guidance avoided the earlier modular-arithmetic reconstruction.  This result retains the stronger theorem for its structural benefit but directs the next timing experiment to a semantically different scalar loop and the next general LTG work to machine-word arithmetic adapters.

## Measurement and controls

The primary performance metric is elapsed time from the Stage 5 heading to the first proof accepted by the independent outer check, measured through `process.hrtime.bigint`.  Accepted proof lines, explicit syntax, local scaffolding, repeated derivations, and shared theorem applications provide secondary structural evidence; raw source bytes, word length, and identifier length do not measure proof complexity.  `benchmark.json` records and checks the ten Codex 0.146.0 packages, while the retained scalar directories contain the Codex 0.147.0 packages with schema-two task identities and complete telemetry.

The host wall clock changed during both isolated runs.  The calls-only control's UTC timestamps span about two hours while its monotonic total is 2,645.818 seconds, and the scalar candidate's timestamps span nearly four hours while its monotonic total is 3,894.697 seconds.  The comparison therefore uses `totalMilliseconds`, `codexSessionMilliseconds`, and `outerAcceptanceMilliseconds`, rather than subtracting the recorded UTC timestamps.

The historical packages record Codex CLI version `0.146.0`, while the ten scalar packages record artifact-proof CLI version `0.147.0` and preserve the earlier task identities under stage-report schema two.  The first two historical packages did not record the Codex model or reasoning setting, and the checker reports that limitation on every comparison.  Proof packages generated after telemetry was added contain `proof-telemetry.json`, which separates Codex-session time and outer-acceptance time while retaining the Stage 5 total as the authoritative metric.

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
