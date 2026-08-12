# Benchmark evidence

This directory preserves proof-generation measurements, accepted proof packages, rejected candidates, censored runs, journals, and comparison metadata.  The archive records evidence used to decide whether an annotation, theorem, tactic, starter, or retrieval rule belongs in the shared system.  A slower or failed run remains useful when it identifies a general proof boundary or prevents selective reporting.

| Series | Retained run directories | Artifact | Evidence covered |
|--------|-------------------------:|----------|------------------|
| [Demo 1 prime factors](leanexegen/demo1-array/README.md) | 20 | `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` | Word-address, allocator, singleton-result, scalar-descriptor, transition, and scalar-entry comparisons. |
| [Demo 6 Euclidean GCD](leanexegen/demo6-gcd42/README.md) | 8 | `8126a2d03d514dd1335250b05fc9a1f9b89b84b55cc5b4d3e5a019c0ca6599cf` | Scalar post-test distribution, rejected exit theorem, and structured-LTG retrieval. |
| [Demo 7 counter transfer](leanexegen/demo7-counter-transfer/README.md) | 26 | `f437ebc16e352391ff05ff79d957eb7ef5652424d6d28c3f279e782980eeb7a5` | Arithmetic LTG, checked summaries, composition, starters, context selection, and rejected alternatives. |
| [Demo 8 three accumulators](leanexegen/demo8-three-accumulator/README.md) | 4 | `932262dad153458571234372e49c4142d7a7ea82cff4d09e2f2fd5eb276e4151` | Cross-layout summaries, normalized starters, and direct acceptance. |
| [Demo 9 wrapping sum](leanexegen/demo9-fold-sum/README.md) | 7 | `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5` | Fold support, structured tactics, accepted retrieval, outer rejection, and censored proof tasks. |

The five series contain 65 tracked run directories.  Each series README states the experimental controls, outcomes, timing treatment, proof structure, and retention decision, while package files bind accepted measurements to exact artifact and proof identities.  Diagnostic directories without a complete package identify their candidate, journal, failure, or censoring boundary explicitly.

Repeated package files do not imply repeated logical evidence: Git stores identical blobs once, while each directory preserves the context presented during that run.  Deduplication therefore requires equality of the artifact, proof, journal, telemetry, task inputs, and reason for retention.  No benchmark evidence is removed during repository housekeeping without such an inventory and an updated series record.

The 2026-08-11 cleanup inventory computed Git tree identities for all 65 tracked benchmark runs and all 23 retained demo experiment packages.  Every complete directory had a distinct tree identity, so the cleanup removed no tracked evidence package as a byte-for-byte duplicate.  This test does not equate semantically related runs whose telemetry, journal, or supplied context differs.
