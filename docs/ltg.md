# Structured LTG catalog

The structured LTG catalog is the proof agent's canonical directory of Lean lemmas, tactics, compiler-motif support, proof methods, and worked examples.  It stores each entry once and generates overlapping category indexes for file-based retrieval.  A proof agent searches those indexes with ordinary tools and opens only entries relevant to the current artifact and proof state.

## Repository structure

| Path | Contents |
|------|----------|
| `ltg/categories.json` | Root category list with a title and search scope for each category. |
| `ltg/categories/<category>/tools.jsonl` | Generated one-record-per-entry index containing summaries, features, annotation kinds, modules, declarations, and search aliases. |
| `ltg/entries/<entry>/entry.json` | Canonical machine-readable identity, classification, premises, result, consumers, relations, and exclusions. |
| `ltg/entries/<entry>/README.md` | Proof guidance, application order, limitations, and interpretation for one entry. |
| `proofs/talos/lean/Project/ProofKit/LTGCheck.lean` | Generated imports and `#check` commands for every declaration advertised by the catalog. |
| `tools/ltg` | Catalog rebuild, consistency check, and size report. |

An entry may appear in several category indexes, while its canonical metadata and prose remain under `ltg/entries`.  Index records include exact declaration names and derived search terms because proof agents often begin with a generated annotation kind, a residual Lean declaration, or a theorem name rather than a catalog title.  `tools/ltg rebuild` derives every index and the Lean declaration audit from the canonical entries, avoiding independent copies that can disagree.

Each entry separates role, scope, and evidence status.  Role distinguishes checked proof assets, annotation support, guidance, proof-generation mechanisms, and worked examples; scope distinguishes generic semantics, compiler or runtime motifs, and benchmark-local material.  Evidence status informs retrieval and promotion, while narrow checked material remains available as an example unless invalidity, staleness, unsafe disclosure, or duplication provides a specific reason to remove it.

## Proof-agent retrieval

Each artifact-proof workspace contains `LTG/categories.json`, the category indexes, the included canonical entries, and `LTG_TASK.json`.  The prompt directs the agent to start at the category list, search likely indexes with `rg`, inspect summaries before opening entry bodies, and follow `relatedEntries` only when the proof state supports the relation.  The journal records exact queries, entries opened, entries used, entries rejected, and missing catalog support.

```text
rg -n 'scalar-post-test|postTestProgram_spec|gcd|remainder' LTG/categories
sed -n '1,220p' LTG/entries/scalar-post-test-loop/entry.json
sed -n '1,240p' LTG/entries/euclidean-gcd-loop/README.md
```

This protocol keeps catalog size separate from prompt size.  The agent initially receives a short retrieval instruction, the root category file, and access to the file tree; it does not receive every entry's prose in its language-model context.  Searchable JSONL records support local filtering before the agent spends context on a full entry.

`LTG_TASK.json` binds the visible catalog view to the task.  It records the exact artifact digest used for exclusion, derivative groups supplied by the orchestrator, sorted included and excluded entry identifiers, their counts, and a digest over every visible LTG file.  An exact-artifact worked example therefore cannot enter a measured proof workspace through another category index.

The current orchestrator supplies the artifact digest automatically.  The catalog library also implements derivative-group exclusion, although automatic artifact-to-derivative classification does not yet exist.  Until that classification exists, an evaluation that covers close derivatives must pass the relevant group explicitly or review the packaged exclusion record.

## Validation and package identity

Catalog checks reject malformed metadata, unsupported proof-kit imports, unknown categories or related entries, stale generated indexes, and stale Lean declaration checks.  The generated `LTGCheck.lean` imports the advertised proof modules and asks Lean to resolve every declaration, which catches misspelled names and removed theorems before a proof session.  The repository checks are:

```text
tools/ltg check
node test/ltg.js
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck
```

Schema-7 proof packages archive the exact filtered view under `ltg/` and its manifest as `ltg-task.json`.  Package validation recomputes the catalog digest, checks category index references, requires every included entry to be indexed and present, and rejects an archived body for any excluded entry.  This archive reconstructs the proof agent's available LTG context without requiring the current repository catalog to match historical guidance.

The checked `Behavior.lean` theorem remains the authority for verification.  LTG metadata and prose grant no imports and discharge no proof obligations; Lean checks imported declarations, generated region equalities connect compiler motifs to exact decoded instructions, and the package verifier rebuilds the artifact theorem.  The proof-kit README remains an available human reference and part of the checked proof-kit source identity, while the proof prompt names the structured LTG tree as the canonical discovery path.

## Fixed-artifact evidence

Two Demo 6 runs held the formal specification, source, 1,770-byte WASM artifact, decoded program, toolchain, and checked proof kit fixed.  The first structured run found the scalar-loop, singleton-wrapper, and residual-normalization entries, rejected unrelated counter examples from their summaries, and revealed two catalog defects: declaration names were absent from index search terms, and no Euclidean-GCD guidance existed.  Its independently verified 141-line proof took 880.514 seconds, compared with the retained 510.885-second median.

The revised indexes added declaration and module aliases, and a provisional Euclidean-GCD entry recorded the invariant, measure, and arithmetic lemmas.  The second agent searched four category indexes, selected four relevant entries, opened only those entries, rejected counter, map, and filter entries from summaries, and used every selected entry in an independently verified 153-line proof.  Stage 5 took 649.557 seconds, which improved on the first structured run by 26.2 percent but remained 27.1 percent above the retained median.

These runs establish selective discovery, exclusion, related-entry use, and successful proof construction.  They do not establish lower proving time, and the current catalog is too small to measure retrieval behavior at thousands of entries.  The [Demo 6 benchmark record](../benchmarks/leanexegen/demo6-gcd42/README.md) preserves both packages, journals, accepted proofs, and telemetry.

## Growth and evaluation

Catalog growth should preserve small root files, bounded index records, canonical entry bodies, and overlapping categories.  Large categories can split into subcategories or shard JSONL indexes without changing entry identity; the root category description should tell the agent which shard to search.  Search aliases should come from declarations, modules, annotation kinds, features, and terms observed in journals rather than from copied proof prose.

Every proof-time iteration should review the journal, accepted proof, and telemetry together.  Journal searches reveal missing aliases, irrelevant ranking, unhelpful related links, absent abstractions, and guidance that does not match the checked theorem boundary.  Evaluation should include fixed-artifact repeats, diverse demos, held-out artifacts, and synthetic large-catalog retrieval tests, with proving time as the primary metric and accepted proof structure as secondary evidence.

Promotion requires evidence appropriate to an entry's role.  A checked theorem can remain provisional after one consumer, while a worked example may remain searchable because its proof organization teaches a useful method.  Automatic selection should favor generic or recurring checked support, but file-based retrieval may retain narrow examples with exact-artifact and derivative exclusions.

The repository test places the real scalar-loop and Euclidean entries among 9,998 synthetic records in one JSONL category index.  The Demo 6 query returned only those two records and less than 10 KB of output; observed local searches completed in tens of milliseconds, although the test imposes no timing bound.  This test covers file-level selectivity rather than agent judgment, so later held-out proofs and larger real catalogs must still measure files opened, context consumed, and time before the first useful theorem application.
