# LTG metrics

The structured LTG is a versioned knowledge artifact whose retrieval units are canonical entries.  An entry may combine guidance, checked declarations, annotation support, a proof-generation mechanism, and worked-example evidence, so those inventories overlap.  The metrics therefore report 22 entries and several orthogonal inventories rather than adding lemmas, tactics, and guidance into a misleading total.

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

Canonical entry content consists of the 44 files below `ltg/entries`, while the canonical catalog also includes the root README and category definitions.  Generated JSONL indexes repeat selected metadata to support bounded file search, so their bytes belong to physical distribution cost rather than unique entry content.  A filtered artifact-proof task can exclude worked examples and produce a smaller bundle; the snapshot measures the complete unfiltered catalog.

## Snapshot: 2026-08-10

This snapshot uses LTG and proof-kit content at repository revision `1dab8e818463f2303ef60eb206dacbf6bde55461`.  Its complete task-bundle digest is `7e8be298632a9187776eb60878d277fa2ae635b93d37943f13e08908a48525a6`, which identifies the exact catalog files presented to an unfiltered proof task.  Later reports can compare the dated revision, bundle digest, and schema version before comparing counts.

| Catalog measure | Value |
|-----------------|------:|
| Categories | 7 |
| Canonical entries | 22 |
| Category memberships | 83 |
| Mean memberships per entry | 3.773 |
| Membership range per entry | 2–5 |
| Entries in multiple categories | 22 |
| Role assignments | 48 |
| Generic-semantics entries | 6 |
| Compiler-runtime-motif entries | 12 |
| Benchmark-local entries | 4 |
| Promoted entries | 8 |
| Provisional entries | 14 |
| Rejected entries | 0 |

The `compiler-motifs` and `proof-construction` categories each contain 17 entries, `arrays` contains 16, and `loops` contains 15.  The `allocation` and `memory` categories each contain 7 entries, while `worked-examples` contains 4.  The JSON output also reports all 19 nonzero pair intersections, including 13 entries shared by `arrays` and `compiler-motifs`, so category growth can be assessed without treating repeated index records as new knowledge.

| Entry coverage measure | Value |
|------------------------|------:|
| Entries carrying guidance | 18 |
| Guidance-only entries | 1 |
| Entries carrying checked proof assets | 16 |
| Entries carrying annotation support | 8 |
| Entries carrying a proof-generation mechanism | 2 |
| Worked-example entries | 4 |
| Entries with an executable role | 17 |
| Entries naming Lean modules and declarations | 22 |
| Entries naming a local proof-kit declaration | 21 |
| Entries importing a tactic-bearing module | 6 |

The catalog contains 63 unique feature strings across 127 assignments and 12 unique annotation kinds across 33 assignments.  Every entry names at least one annotation kind, while the scalar post-test and array-fold annotations each bind 7 entries.  The catalog records 61 consumer assignments across Demos 1 through 10, and every entry has at least one recorded consumer.

| Lean-support measure | Indexed by entries | Complete supplied proof kit |
|----------------------|-------------------:|----------------------------:|
| Module references | 31 assignments, 18 unique | 27 modules |
| Declaration references | 72 assignments, 58 unique | 371 source headers |
| Public named local declarations | 50 indexed | 322 available |
| Theorem headers | 37 indexed | 178 total |
| Lemma headers | 0 indexed | 0 total |
| Definition headers | 13 indexed | 151 total |
| Other source headers | 0 indexed | 42 total |
| Tactic definitions | No structured entry field | 29 macro definitions |
| Distinct tactic commands | No structured entry field | 27 commands |
| Tactic-bearing modules | 6 entries import one | 11 modules |

Entries mention 18 of the 27 supplied proof-kit modules, a module coverage ratio of 0.667.  Their declaration arrays expose 50 of 322 public named local source declarations, a lexical discoverability ratio of 0.155, and reference 8 additional imported declarations whose kinds this command does not infer.  The remaining proof-kit source is usable through imports but absent from structured declaration retrieval, which identifies a substantial indexing backlog rather than missing Lean implementation.

The complete proof kit has 371 recognized source headers: 178 `theorem`, 151 `def`, 29 `macro`, 7 `inductive`, 5 `structure`, and 1 `abbrev`.  Of these headers, 351 are public and 20 are private.  The source contains no recognized `lemma`, `class`, `instance`, `opaque`, or `elab` header at this revision.

Tactic coverage currently has a metadata limitation.  The proof kit defines 29 tactic macros representing 27 distinct command tokens, but `entry.json` has no structured tactic-name field, so the metrics can only report that 6 entries import at least one of the 11 tactic-bearing modules.  Adding an explicit tactic inventory to a later entry schema would permit direct retrieval coverage, use tracking, and stale-name validation without inferring relationships from prose.

| Content measure | Files | Bytes |
|-----------------|------:|------:|
| Canonical entry content | 44 | 67,128 |
| Canonical catalog | 46 | 69,934 |
| Catalog Markdown | 23 | 36,934 |
| Metadata JSON | 23 | 33,000 |
| Generated category indexes | 7 | 99,700 |
| Physical catalog | 53 | 169,634 |
| Complete unfiltered task bundle | 53 | 169,634 |
| Proof-kit Lean sources | 27 | 325,170 |
| Proof-kit README | 1 | 42,507 |
| Generated declaration check | 1 | 4,002 |
| Combined physical knowledge | 81 | 537,311 |

Generated indexes account for 99,700 of the physical catalog's 169,634 logical bytes.  This duplication buys search locality and does not increase the 67,128-byte canonical entry inventory.  The combined total counts each physical task-catalog and proof-kit file once and excludes the generated declaration check, whose size appears on its own row.

The relation graph contains 92 directed related-entry links, including 31 reciprocal pairs and 30 asymmetric links, with no entry isolated from the graph.  Four worked examples carry exclusions covering four exact artifact digests and three derivative groups.  Catalog validation found no dangling category, allowed-module, or related-entry reference, and the local source inventory found no missing `Project.ProofKit` declaration name.

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
