# LTG and CLOB Retrospective

This retrospective records the repository evidence through 2026-08-18.  It covers the development of shared lemmas, tactics, guidance, compiler annotations, generated proof adapters, structured LTG retrieval, and the eight CLOB artifact proofs.  It separates measured proof-generation changes from improvements in proof structure, retrieval, and supported program behavior.

## LTG scope and measurement

The project first used LTG to mean the combined collection of lemmas, tactics, and guidance supplied to a proving agent.  That work later grew to include compiler annotations, exact annotation-to-artifact equalities, generated compositions, deterministic starters, and a structured retrieval catalog.  The searchable catalog is one part of the system, so measurements of the combined system do not establish the effect of catalog retrieval in isolation.

The primary time measure is Stage 5 elapsed time from the proof-stage heading to the first candidate accepted by the independent outer check.  Fixed-artifact comparisons preserve the formal specification, source, WASM bytes, decoded Talos program, theorem statement, toolchain, and task settings while changing the supplied proof support.  Proof lines, edited candidates, local scaffolding, repeated derivations, and shared theorem use provide secondary evidence, while raw bytes and identifier lengths do not measure proof complexity.

## Combined LTG results

The strongest time reductions occur when a recurring compiler shape receives a checked semantic theorem, an exact annotation match, and a starter that composes them.  Six later fixed-artifact comparisons report reductions from 32.1 to 95.4 percent, with a median near 65 percent.  These percentages combine proof-library, annotation, recipe, guidance, and orchestration changes, and the different artifacts prevent treating their median as a causal estimate for arbitrary WASM.

| Artifact | Baseline Stage 5 | Retained result | Reduction | Proof lines | Evidence |
|----------|-----------------:|----------------:|----------:|------------:|----------|
| [Demo 4: bounded array map](../demos/demo-4/README.md) | 2,364.735 s | 109.165 s median | 95.4% | 457 to 66 | Three final runs over one fixed artifact. |
| [Demo 5: bounded array filter](../demos/demo-5/README.md) | 1,635.679 s | 90.745 s median | 94.5% | 969 to 70 | Three final runs over one fixed artifact. |
| [Demo 6: Euclidean GCD loop](../benchmarks/leanexegen/demo6-gcd42/README.md) | 1,056.072 s | 510.885 s median | 51.6% | 191 to 157 median | Three retained runs over one fixed artifact. |
| [Demo 7: counter transfer](../benchmarks/leanexegen/demo7-counter-transfer/README.md) | 577.039 s | 125.103 s median | 78.3% | 171 to 67 | Three direct-starter runs over one fixed artifact. |
| [Demo 8: three counters](../benchmarks/leanexegen/demo8-three-accumulator/README.md) | 313.253 s | 212.727 s | 32.1% | 70 to 67 | One out-of-sample direct-starter run. |
| [Demo 9: wrapping-sum fold](../demos/demo-9/README.md) | 3,431.870 s | 1,638.250 s | 52.3% | 493 to 650 | Later accepted stateful run; its learned theorem was inspected and rejected. |

The earlier [Demo 1 benchmark](../benchmarks/leanexegen/demo1-array/README.md) provides another controlled progression over one 1,938-byte artifact.  Its initial proof-kit run took 3,516.775 seconds, while the combined fixed-array allocator and singleton-result theorem produced a 489.993-second median, a reduction of about 86 percent.  Later Demo 1 experiments used another Codex series and isolate scalar annotations, so the benchmark reports those comparisons separately.

Demo 4 and Demo 5 provide the largest reductions because their final theorems cover complete bounded map and filter wrappers.  Those theorems parameterize the array bound and scalar operation or predicate, but they still describe narrow compiler families.  They establish the value of whole-region semantic interfaces without supporting a claim about unrelated WASM control flow.

Demo 6 supplies stronger evidence for a recurring loop motif.  Its scalar post-test annotation and generated entry adapter reduced the three-run median by 51.6 percent, removed one raw loop rule and seventeen explicit instruction-cons steps, and reduced edited candidates from nine to a median of two.  Demo 7 and Demo 8 then transferred related scalar summaries and complete wrapper compositions to different accumulator layouts, although the final zero-Codex results also depend on direct acceptance of a complete generated starter.

Demo 9 shows the remaining difficulty of structured array loops.  Its fastest retained run is 52.3 percent faster than baseline, but the accepted proof grew from 493 to 650 lines and still took more than twenty-seven minutes.  The proving agent rejected the learned theorem in that run, so the result does not measure a learning benefit.  Demo 10 and Demo 11 establish transfer across wrapping addition, wrapping multiplication, and bitwise XOR, while several traversal, suffix, frame-accessor, and composition experiments increased proof time or proof size.

## Structured catalog results

Repository commit `0745b82` introduced structured LTG retrieval on 2026-08-09.  The catalog gives each proof asset one canonical entry, generates overlapping category indexes, records declarations, tactics, features, consumers, related entries, and artifact exclusions, and packages a filtered view for each proof task.  The indexes let an agent inspect compact summaries before opening entry files, while the proof journal records its retrieval decisions.

The structured catalog alone has not established a proof-time reduction against the best pre-catalog configuration.  In Demo 6, the revised structured run improved from 880.514 to 649.557 seconds, a 26.2 percent reduction from the first structured run, but remained 27.1 percent slower than the 510.885-second retained median.  In the early Demo 9 series, fold annotation and structured LTG reduced 3,431.870 seconds to 3,188.251 seconds, while later traversal and tactic screens included censored runs and a candidate rejected by the independent outer check.

The catalog has established selective discovery and bounded file retrieval.  A repository test placed the scalar-loop and Euclidean entries among 9,998 synthetic records, and the query returned those two entries with less than 10 KB of output in tens of milliseconds.  This test measures file selection rather than theorem choice, proof construction, or Lean elaboration.

The dated [LTG metrics](ltg-metrics.md) report seven categories and twenty-four canonical entries covering all eleven demos.  The entries index 84 unique declaration names, including 76 local ProofKit declarations, and five of the twenty-seven supplied tactic commands.  The ProofKit contains 339 public named declarations, so structured declaration retrieval covers 22.4 percent of that snapshot's inventory.  The physical catalog occupies 224,082 bytes, and the catalog plus supplied ProofKit sources and documentation occupy 608,132 bytes.

## Causes of improvement and failure

Large improvements came from moving repeated instruction-level reasoning into checked semantic theorems.  Exact annotation equalities connect those theorems to the decoded artifact, while generated adapters present the theorem in the frame and continuation shape required by the public proof.  Deterministic starters remove agent search when those components already establish the complete behavior theorem.

The catalog helps only when a useful theorem or method exists and the residual goal exposes terms that retrieve it.  Journals record failures caused by large generated frames, dependent premise inference, broad simplification, expensive continuation goals, missing frame projections, and theorem boundaries that preserved too much machine state.  Several structurally shorter proofs took longer because the agent spent more time matching or composing the supplied abstraction.

The current evidence supports large gains for recognized maps, filters, singleton wrappers, scalar post-test loops, allocation regions, and selected fold phases.  The fold demos share closely related wrappers and control flow, so addition, multiplication, and XOR do not test a different accumulator or loop structure.  A structurally different held-out artifact remains necessary to measure transfer beyond those compiler families.

The compiler proves that successful scalar-descriptor reification agrees with its public emitter.  The retained artifact proof instead checks the descriptor against the independently decoded WASM region and applies neutral ProofKit semantics, so it does not import the compiler-side theorem.  Current LTG measurements therefore show the value of compiler-generated evidence and independent artifact checks, but they do not measure direct use of a compiler-correctness theorem in a WASM proof.

## CLOB verification results

The CLOB source implements arrays of `Order`, `Trade`, and `Level` structures together with search, cancellation, insertion, matching, aggregation, and multiple result arrays.  The proof inventory contains input-generic theorems for `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth`.  Exact-artifact packages connect each behavioral theorem to frozen WASM bytes through checked decoding, validation, and Talos translation.

| Export | Established behavior |
|--------|----------------------|
| `quote` | Returns the six fields of the source quote fold for every represented order array and preserves the store. |
| `cancel` | Distinguishes missing and found identifiers, returns a borrowed or fresh book as appropriate, and states exact allocator effects. |
| `findBest` | Returns the source optional index and proves eligibility, best price, and first-index selection among equal-price makers. |
| `postOnly` | Covers invalid, crossing, and append branches with exact statuses, books, empty trades, ownership, and memory effects. |
| `matchFuel` | Returns the source remaining quantity and owned result arrays while tracking free-list state, allocation, release, and quantity conservation. |
| `limit` | Connects matching and residual-order insertion to exact status, book, trades, ownership, allocator state, and memory framing. |
| `market` | Reuses the matcher result after the unlimited-price transformation and proves both valid and invalid outcomes. |
| `depth` | Returns owned bid and ask level arrays and proves modular per-price aggregation with a bounded natural-number interpretation. |

## CLOB findings

The main proof burden comes from memory semantics rather than the trading calculations.  The difficult obligations describe represented structured arrays, borrowed and owned roots, allocator globals, free-list search and mutation, reference counting, release, page bounds, copied regions, and disjoint writes.  The application lemmas then identify best-price choice, stable tie handling, quantity conservation, and price-level aggregation.

A useful CLOB theorem states more than returned scalar and array values.  It records whether each result is borrowed or newly owned, the exact allocation and release counters, page preservation, free-list representation, and the memory regions that remain unchanged.  These physical facts allow one verified call to serve as the premise of the next allocating or releasing call.

Resource bounds form part of the behavioral specification.  The `matchFuel`, `limit`, `market`, and `depth` proofs require explicit fuel, heap reserve, page, and allocation-budget conditions to establish termination without a trap.  The loop invariant carries the source transition, represented heap objects, selected generated locals, memory frame, ownership state, and remaining budget together.

Large CLOB proofs require bottom-up semantic boundaries.  The successful structure gives each reachable helper a theorem, divides a large function into calls, loops, allocator phases, copies, and result construction, and connects those pieces through small frame records.  Whole-function reduction, literal generated-state equalities, and large continuation goals caused long elaboration, memory pressure, or timeouts without diagnostics.

CLOB produced reusable results for fixed arrays, structured element representations, flat-word reads, region framing, first-match scans, allocation, free-list traversal, reference counting, release, copying, direct calls, loop rules, and store-preserving helpers.  The `market` proof reuses the matcher and limit proof chain rather than rebuilding their call closure.  The depth proof adds a general pattern for representing logical pairs over flat word arrays and preserving a source region while copying into a disjoint target.

The eight CLOB case directories contain 49,290 Lean lines in 240 files after excluding generated `Program.lean` and `Artifact*.lean` modules.  `matchFuel` and `limit` account for 33,586 lines, or 68.1 percent of this source.  Their size made small proof-module boundaries necessary for diagnostic feedback and bounded elaboration.

| Case | Handwritten Lean files | Lines |
|------|-----------------------:|------:|
| `quote` | 3 | 585 |
| `cancel` | 2 | 1,146 |
| `findBest` | 4 | 1,502 |
| `postOnly` | 19 | 4,896 |
| `matchFuel` | 71 | 18,100 |
| `limit` | 86 | 15,486 |
| `market` | 22 | 1,553 |
| `depth` | 33 | 6,022 |
| **Total** | **240** | **49,290** |

## Relationship between CLOB and LTG

CLOB supplied evidence for many proof methods now recorded in [Artifact-Proof Strategies](proof-strategies.md) and for shared runtime results used by ProofKit.  Its case-local modules remain outside the `leanexegen` proof-agent allowlist, so a generated proof cannot import a CLOB theorem as its answer.  The import audit enforces that separation, while LTG exposes selected general declarations and methods through the catalog and allowed ProofKit modules.

Current LTG proof generation has not reproduced a CLOB-grade proof.  The completed CLOB theorems establish that direct WASM reasoning can cover structured, allocating application code, while the demo benchmarks establish that shared support can reduce proving time for smaller recurring compiler shapes.  A new structured and allocating artifact, proved with only the general results distilled from CLOB, would connect those two bodies of evidence.

The CLOB proof chain also does not depend on a general compiler-correctness theorem.  Each exact-artifact package embeds the frozen bytes, decodes and validates them, proves equality with the Talos program used by the behavioral theorem, and checks that theorem.  This construction proves the named binary's behavior without claiming that every accepted Lean program lowers correctly.

## Conclusions

The combined LTG system has reduced proof-generation time and proof size for several recognized compiler families.  The largest reductions come from checked whole-region semantics and generated composition, while structured retrieval supplies selective access, exclusions, and reproducible evidence about what the agent consulted.  Catalog retrieval in isolation has mixed timing evidence and remains incomplete relative to the available ProofKit.

CLOB established a broader semantic boundary than the current demos.  It requires exact ownership, allocator, release, free-list, memory-frame, and resource claims in addition to application results.  Its general proof patterns form a source for future ProofKit and LTG entries, while its size shows that successful automation must reduce both agent search and Lean elaboration boundaries.
