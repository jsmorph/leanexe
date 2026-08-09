# LTG metrics

The structured LTG is a versioned knowledge artifact whose retrieval units are canonical entries.  An entry may combine guidance, checked declarations, annotation support, a proof-generation mechanism, and worked-example evidence, so those inventories overlap.  The metrics therefore report 15 entries and several orthogonal inventories rather than adding lemmas, tactics, and guidance into a misleading total.

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

Canonical entry content consists of the 30 files below `ltg/entries`, while the canonical catalog also includes the root README and category definitions.  Generated JSONL indexes repeat selected metadata to support bounded file search, so their bytes belong to physical distribution cost rather than unique entry content.  A filtered artifact-proof task can exclude worked examples and produce a smaller bundle; the snapshot measures the complete unfiltered catalog.

## Snapshot: 2026-08-09

This snapshot uses LTG and proof-kit content at repository revision `0210e7d8099c40e1bdc866f6552aac4a9e82b81c`.  Its complete task-bundle digest is `0c609bc7e65ffc742108489438446f686c4683c2929a2695cefdb2466b90ea89`, which identifies the exact catalog files presented to an unfiltered proof task.  Later reports can compare the dated revision, bundle digest, and schema version before comparing counts.

| Catalog measure | Value |
|-----------------|------:|
| Categories | 7 |
| Canonical entries | 15 |
| Category memberships | 56 |
| Mean memberships per entry | 3.733 |
| Membership range per entry | 2–5 |
| Entries in multiple categories | 15 |
| Role assignments | 30 |
| Generic-semantics entries | 5 |
| Compiler-runtime-motif entries | 6 |
| Benchmark-local entries | 4 |
| Promoted entries | 7 |
| Provisional entries | 8 |
| Rejected entries | 0 |

The `arrays` category contains 12 entries, while `compiler-motifs`, `loops`, and `proof-construction` each contain 10.  The `allocation` and `memory` categories each contain 5 entries, and `worked-examples` contains 4.  The JSON output also reports all 19 nonzero pair intersections, including 9 entries shared by `arrays` and `compiler-motifs`, so category growth can be assessed without treating repeated index records as new knowledge.

| Entry coverage measure | Value |
|------------------------|------:|
| Entries carrying guidance | 11 |
| Guidance-only entries | 1 |
| Entries carrying checked proof assets | 9 |
| Entries carrying annotation support | 5 |
| Entries carrying a proof-generation mechanism | 1 |
| Worked-example entries | 4 |
| Entries with an executable role | 10 |
| Entries naming Lean modules and declarations | 15 |
| Entries naming a local proof-kit declaration | 14 |
| Entries importing a tactic-bearing module | 4 |

The catalog contains 44 unique feature strings across 77 assignments and 9 unique annotation kinds across 20 assignments.  Every entry names at least one annotation kind, while the scalar post-test annotation has the broadest binding at 5 entries.  The catalog records 34 consumer assignments across Demos 1 through 9, and every entry has at least one recorded consumer.

| Lean-support measure | Indexed by entries | Complete supplied proof kit |
|----------------------|-------------------:|----------------------------:|
| Module references | 21 assignments, 11 unique | 23 modules |
| Declaration references | 39 assignments, 31 unique | 328 source headers |
| Public named local declarations | 25 indexed | 284 available |
| Theorem headers | 19 indexed | 156 total |
| Lemma headers | 0 indexed | 0 total |
| Definition headers | 6 indexed | 135 total |
| Other source headers | 0 indexed | 37 total |
| Tactic definitions | No structured entry field | 24 macro definitions |
| Distinct tactic commands | No structured entry field | 22 commands |
| Tactic-bearing modules | 4 entries import one | 11 modules |

Entries mention 11 of the 23 supplied proof-kit modules, a module coverage ratio of 0.478.  Their declaration arrays expose 25 of 284 public named local source declarations, a lexical discoverability ratio of 0.088, and reference 6 additional imported declarations whose kinds this command does not infer.  The remaining proof-kit source is usable through imports but absent from structured declaration retrieval, which identifies a substantial indexing backlog rather than missing Lean implementation.

The complete proof kit has 328 recognized source headers: 156 `theorem`, 135 `def`, 24 `macro`, 7 `inductive`, 5 `structure`, and 1 `abbrev`.  Of these headers, 308 are public and 20 are private.  The source contains no recognized `lemma`, `class`, `instance`, `opaque`, or `elab` header at this revision.

Tactic coverage currently has a metadata limitation.  The proof kit defines 24 tactic macros representing 22 distinct command tokens, but `entry.json` has no structured tactic-name field, so the metrics can only report that 4 entries import at least one of the 11 tactic-bearing modules.  Adding an explicit tactic inventory to a later entry schema would permit direct retrieval coverage, use tracking, and stale-name validation without inferring relationships from prose.

| Content measure | Files | Bytes |
|-----------------|------:|------:|
| Canonical entry content | 30 | 36,836 |
| Canonical catalog | 32 | 39,642 |
| Catalog Markdown | 16 | 18,836 |
| Metadata JSON | 16 | 20,806 |
| Generated category indexes | 7 | 60,977 |
| Physical catalog | 39 | 100,619 |
| Complete unfiltered task bundle | 39 | 100,619 |
| Proof-kit Lean sources | 23 | 292,047 |
| Proof-kit README | 1 | 37,519 |
| Generated declaration check | 1 | 2,157 |
| Combined physical knowledge | 63 | 430,185 |

Generated indexes account for 60,977 of the physical catalog's 100,619 logical bytes.  This duplication buys search locality and does not increase the 36,836-byte canonical entry inventory.  The combined total counts each physical task-catalog and proof-kit file once and excludes the generated declaration check, whose size appears on its own row.

The relation graph contains 39 directed related-entry links, including 11 reciprocal pairs and 17 asymmetric links, with no entry isolated from the graph.  Four worked examples carry exclusions covering four exact artifact digests and three derivative groups.  Catalog validation found no dangling category, allowed-module, or related-entry reference, and the local source inventory found no missing `Project.ProofKit` declaration name.

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
