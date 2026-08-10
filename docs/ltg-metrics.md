# LTG metrics

The structured LTG is a versioned knowledge artifact whose retrieval units are canonical entries.  An entry may combine guidance, checked declarations, annotation support, a proof-generation mechanism, and worked-example evidence, so those inventories overlap.  The metrics therefore report 17 entries and several orthogonal inventories rather than adding lemmas, tactics, and guidance into a misleading total.

## Counting model

`tools/ltg metrics` validates the catalog before producing deterministic JSON.  The command reads canonical entry metadata and guidance, generated category indexes, and every Lean module in the proof-kit allowlist.  It neither invokes Lean nor changes generated files, which keeps routine measurement independent of the machine-wide Lean execution lane.

| Inventory | Counting rule |
|-----------|---------------|
| Retrieval units | Ordinary directories under `ltg/entries`, after full schema validation. |
| Categories and memberships | Categories come from `categories.json`; each entry-to-category assignment is one membership. |
| Roles, scopes, and evidence | Values in canonical `entry.json` files; one entry can carry several roles. |
| Guidance | Entries carrying the `guidance` role; `guidanceOnlyEntries` requires that to be the entry's sole role. |
| Executable role | An entry carrying `checked-proof-asset` or `proof-generation-mechanism`; this measures declared role, not theorem use in a proof run. |
| Declaration references | Every string in an entry's `declarations` array; the unique count deduplicates the same name across entries. |
| Local declaration kind | A unique declaration name whose fully qualified name matches a public source header in an allowed `Project.ProofKit` module. |
| Proof-kit declaration header | A line-oriented source header beginning with a supported Lean declaration keyword after whitespace and supported modifiers. |
| Tactic definition | A `macro` or `elab` source header whose header ends in `: tactic` before its first `=>`; distinct commands use the first quoted command token. |
| Annotation binding | One entry-to-annotation-kind assignment from `annotationKinds`; the count does not assert that the compiler emits the annotation. |
| Consumer binding | One entry-to-consumer string from `consumers`; the count records catalog evidence and does not infer use from proof text. |
| Catalog Markdown | The root README and every entry README, independent of the entries' semantic roles. |
| Canonical bytes | UTF-8 logical bytes in the root README, `categories.json`, and each canonical entry file, with every entry stored once. |
| Physical catalog bytes | Canonical bytes plus generated category-index bytes as they exist under `ltg/`. |
| Combined knowledge bytes | Physical catalog bytes plus the allowed proof-kit Lean sources and proof-kit README; generated `LTGCheck.lean` is reported separately. |

The source-header inventory recognizes `theorem`, `lemma`, `def`, `abbrev`, `opaque`, `structure`, `class`, `inductive`, `instance`, `macro`, and `elab`.  It counts private source headers but reports them separately, and it excludes constructors, generated recursors, structure projections, local bindings, and declarations inherited from imports.  Lean's generated `LTGCheck.lean` remains the semantic existence check for every advertised declaration, while this metrics command classifies only names supported by catalog metadata or a matching local source header.

Canonical entry content consists of the 34 files below `ltg/entries`, while the canonical catalog also includes the root README and category definitions.  Generated JSONL indexes repeat selected metadata to support bounded file search, so their bytes belong to physical distribution cost rather than unique entry content.  A filtered artifact-proof task can exclude worked examples and produce a smaller bundle; the snapshot measures the complete unfiltered catalog.

## Snapshot: 2026-08-09

This snapshot uses LTG and proof-kit content at repository revision `79d4375c59556914b9b6f132640919aebdc2317c`.  Its complete task-bundle digest is `cefdccc1d6ef77f98e92ca2618e033563233b56b76bd1450c917d2b79e6c654c`, which identifies the exact catalog files presented to an unfiltered proof task.  Later reports can compare the dated revision, bundle digest, and schema version before comparing counts.

| Catalog measure | Value |
|-----------------|------:|
| Categories | 7 |
| Canonical entries | 17 |
| Category memberships | 66 |
| Mean memberships per entry | 3.882 |
| Membership range per entry | 2–5 |
| Entries in multiple categories | 17 |
| Role assignments | 34 |
| Generic-semantics entries | 5 |
| Compiler-runtime-motif entries | 8 |
| Benchmark-local entries | 4 |
| Promoted entries | 7 |
| Provisional entries | 10 |
| Rejected entries | 0 |

The `arrays` category contains 14 entries, `compiler-motifs` and `proof-construction` each contain 12, and `loops` contains 11.  The `allocation` category contains 6 entries, `memory` contains 7, and `worked-examples` contains 4.  The JSON output also reports all 19 nonzero pair intersections, including 11 entries shared by `arrays` and `compiler-motifs`, so category growth can be assessed without treating repeated index records as new knowledge.

| Entry coverage measure | Value |
|------------------------|------:|
| Entries carrying guidance | 13 |
| Guidance-only entries | 1 |
| Entries carrying checked proof assets | 11 |
| Entries carrying annotation support | 5 |
| Entries carrying a proof-generation mechanism | 1 |
| Worked-example entries | 4 |
| Entries with an executable role | 12 |
| Entries naming Lean modules and declarations | 17 |
| Entries naming a local proof-kit declaration | 16 |
| Entries importing a tactic-bearing module | 5 |

The catalog contains 48 unique feature strings across 90 assignments and 11 unique annotation kinds across 24 assignments.  Every entry names at least one annotation kind, while the scalar post-test annotation has the broadest binding at 5 entries.  The catalog records 40 consumer assignments across Demos 1 through 9, and every entry has at least one recorded consumer.

| Lean-support measure | Indexed by entries | Complete supplied proof kit |
|----------------------|-------------------:|----------------------------:|
| Module references | 23 assignments, 13 unique | 23 modules |
| Declaration references | 48 assignments, 40 unique | 339 source headers |
| Public named local declarations | 34 indexed | 290 available |
| Theorem headers | 28 indexed | 159 total |
| Lemma headers | 0 indexed | 0 total |
| Definition headers | 6 indexed | 138 total |
| Other source headers | 0 indexed | 42 total |
| Tactic definitions | No structured entry field | 29 macro definitions |
| Distinct tactic commands | No structured entry field | 27 commands |
| Tactic-bearing modules | 5 entries import one | 11 modules |

Entries mention 13 of the 23 supplied proof-kit modules, a module coverage ratio of 0.565.  Their declaration arrays expose 34 of 290 public named local source declarations, a lexical discoverability ratio of 0.117, and reference 6 additional imported declarations whose kinds this command does not infer.  The remaining proof-kit source is usable through imports but absent from structured declaration retrieval, which identifies a substantial indexing backlog rather than missing Lean implementation.

The complete proof kit has 339 recognized source headers: 159 `theorem`, 138 `def`, 29 `macro`, 7 `inductive`, 5 `structure`, and 1 `abbrev`.  Of these headers, 319 are public and 20 are private.  The source contains no recognized `lemma`, `class`, `instance`, `opaque`, or `elab` header at this revision.

Tactic coverage currently has a metadata limitation.  The proof kit defines 29 tactic macros representing 27 distinct command tokens, but `entry.json` has no structured tactic-name field, so the metrics can only report that 5 entries import at least one of the 11 tactic-bearing modules.  Adding an explicit tactic inventory to a later entry schema would permit direct retrieval coverage, use tracking, and stale-name validation without inferring relationships from prose.

| Content measure | Files | Bytes |
|-----------------|------:|------:|
| Canonical entry content | 34 | 46,185 |
| Canonical catalog | 36 | 48,991 |
| Catalog Markdown | 18 | 24,801 |
| Metadata JSON | 18 | 24,190 |
| Generated category indexes | 7 | 74,183 |
| Physical catalog | 43 | 123,174 |
| Complete unfiltered task bundle | 43 | 123,174 |
| Proof-kit Lean sources | 23 | 299,195 |
| Proof-kit README | 1 | 37,519 |
| Generated declaration check | 1 | 2,791 |
| Combined physical knowledge | 67 | 459,888 |

Generated indexes account for 74,183 of the physical catalog's 123,174 logical bytes.  This duplication buys search locality and does not increase the 46,185-byte canonical entry inventory.  The combined total counts each physical task-catalog and proof-kit file once and excludes the generated declaration check, whose size appears on its own row.

The relation graph contains 54 directed related-entry links, including 17 reciprocal pairs and 20 asymmetric links, with no entry isolated from the graph.  Four worked examples carry exclusions covering four exact artifact digests and three derivative groups.  Catalog validation found no dangling category, allowed-module, or related-entry reference, and the local source inventory found no missing `Project.ProofKit` declaration name.

## Regeneration and interpretation

Run the metrics command from the repository root after rebuilding and checking a changed catalog.  The first command rewrites derived indexes and `LTGCheck.lean`, the second checks byte-for-byte freshness, and the third emits the complete measurement record.  Lean verification of advertised declaration names remains a separate repository gate and must use the resource-limited runner.

```text
tools/ltg rebuild
tools/ltg check
tools/ltg metrics
node test/ltg.js
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck
```

Growth should increase canonical entries, indexed declarations, tactic discoverability, consumer diversity, and annotation coverage while preserving validation and bounded retrieval.  Physical bytes and generated-index duplication measure distribution cost, while canonical bytes measure authored knowledge without category repetition.  Evidence maturity, exclusions, category overlap, and consumer bindings give content counts enough context to distinguish a larger catalog from a better-supported one.

The metrics do not establish theorem usefulness, proof success, retrieval precision, or proving time.  Journals, accepted proofs, and telemetry measure those properties, while held-out demos test whether catalog growth transfers beyond its motivating program.  Consumer and annotation fields remain catalog claims until proof telemetry and compiler output confirm their use, and consumer identifiers currently have no separate registry against which to check dangling names.
