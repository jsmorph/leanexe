# Knowledge forest and structured LTG catalogs

The knowledge forest selects separately versioned packages of Lean lemmas, tactics, compiler-motif support, proof methods, and worked examples.  Each package owns a structured LTG catalog that stores each entry once and generates overlapping category indexes for file-based retrieval.  A proof agent starts from the forest, searches selected package indexes with ordinary tools, and opens entries relevant to the current artifact and proof state.

## Repository structure

| Path | Contents |
|------|----------|
| `knowledge/forest.json` | Default package selection for generation and reproof. |
| `<package>/knowledge-package.json` | Package identity, version, maturity, dependencies, catalog root, Lean sources, and entry-bound evidence. |
| `ltg/categories.json` | Root category list with a title and search scope for each category. |
| `ltg/categories/<category>/tools.jsonl` | Generated one-record-per-entry index containing summaries, features, annotation kinds, modules, declarations, and search aliases. |
| `ltg/entries/<entry>/entry.json` | Canonical machine-readable identity, classification, premises, result, consumers, relations, and exclusions. |
| `ltg/entries/<entry>/README.md` | Proof guidance, application order, limitations, and interpretation for one entry. |
| `proofs/talos/lean/Project/ProofKit/LTGCheck.lean` | Generated imports and `#check` commands for every declaration advertised by the catalog. |
| `tools/ltg` | Catalog rebuild, consistency check, and size report. |
| `tools/knowledge` | Forest validation, aggregate statistics, and task-snapshot inspection. |

The existing `ltg/` directory is package `leanexe-core`, version one, in the default forest.  An entry may appear in several category indexes, while its canonical metadata and prose remain under one package's `entries/` directory.  Different forest manifests can select combinations of core, project, compiler, experimental, or run-derived packages without merging their catalogs.  Index records include exact declaration names and derived search terms because proof agents often begin with a generated annotation kind, a residual Lean declaration, or a theorem name rather than a catalog title.

Each entry separates role, scope, and evidence status.  Role distinguishes checked proof assets, annotation support, guidance, proof-generation mechanisms, and worked examples; scope distinguishes generic semantics, compiler or runtime motifs, and benchmark-local material.  Evidence status informs retrieval and promotion, while narrow checked material remains available as an example unless invalidity, staleness, unsafe disclosure, or duplication provides a specific reason to remove it.

## Package selection and retrieval

Each artifact-proof workspace contains `KNOWLEDGE/forest.json`, selected package directories, and `KNOWLEDGE_TASK.json`.  The prompt directs the agent to inspect the forest, search likely package indexes with `rg`, inspect summaries before opening entry bodies, and follow `relatedEntries` only when the proof state supports the relation.  The journal records exact queries, packages and entries opened, entries used, entries rejected, and missing catalog support.

```text
rg -n 'scalar-post-test|postTestProgram_spec|gcd|remainder' \
  KNOWLEDGE/packages/leanexe-core/catalog/categories
sed -n '1,220p' \
  KNOWLEDGE/packages/leanexe-core/catalog/entries/scalar-post-test-loop/entry.json
sed -n '1,240p' \
  KNOWLEDGE/packages/leanexe-core/catalog/entries/euclidean-gcd-loop/README.md
```

This protocol keeps forest size separate from prompt size.  The agent initially receives a short retrieval instruction, the forest and package manifests, and access to the file tree.  Searchable JSONL records support local filtering before the agent spends context on a full entry.

`KNOWLEDGE_TASK.json` binds the visible forest view to the task.  It records each package's identity, version, maturity, dependencies, included and excluded entries, required Lean modules, package digest, and the digest over the complete visible forest.  Exact-artifact filtering removes an excluded entry together with its bound evidence and unreferenced package-local Lean sources.

The orchestrator supplies the artifact digest and selected forest to every current proof run.  The package library also implements derivative-group exclusion, while automatic artifact-to-derivative classification remains absent.  An evaluation covering close derivatives therefore passes the relevant group explicitly or reviews the packaged exclusion record.

## Validation and package identity

Catalog checks reject malformed metadata, unsupported imports, unknown categories or related entries, stale generated indexes, and stale Lean declaration checks.  Forest checks add package identity, dependency, global entry identity, package-local module namespace, source import, evidence binding, and complete file-set validation.  The generated `LTGCheck.lean` imports the core package's advertised proof modules and asks Lean to resolve every declaration.

```text
tools/ltg check
tools/knowledge check
node test/ltg.js
node test/knowledge.js
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck
```

Schema-8 proof packages archive the exact filtered forest under `knowledge/` and its manifest as `knowledge-task.json`.  Package validation recomputes forest and package digests, checks package and category references, validates included entries and sources, and rejects excluded entry bodies or evidence.  Schema-7 packages retain their single-catalog `ltg/` archive and validator.

The checked `Behavior.lean` theorem remains the authority for verification.  Knowledge metadata and prose discharge no proof obligations, while package manifests grant import authority only to archived package-local sources whose paths, imports, and digests pass validation.  Lean checks those sources and the final proof, generated region equalities connect compiler motifs to exact decoded instructions, and the package verifier rebuilds the artifact theorem.

## Stateful learning

Stateful learning turns completed proof work into explicit input artifacts for later work.  An accepted proof package can produce an experimental knowledge package, and promotion can add that package to a self-contained forest snapshot.  A later generation or reproof selects the snapshot by path and archives its filtered contents in the resulting proof package.

| Operation | Produced artifact | Use in subsequent work |
|-----------|-------------------|------------------------|
| Proof generation or reproof | Accepted schema-8 proof package | Supplies the checked proof, journal, annotations, task features, recipes, telemetry, and prior knowledge identity. |
| `learn record` | Experimental worked-example package | Preserves the run for retrieval, comparison, and later analysis. |
| `learn propose` | Experimental candidate package | Distills one guidance entry, worked example, checked lemma, or checked tactic from the run and its archived knowledge context. |
| Review and `learn promote` | Promoted package inside a new forest snapshot | Makes the selected candidate available to later runs through `--knowledge`. |
| Later generation or reproof | New proof package | Records which promoted packages and filtered entries were available and which checked modules the proof used. |

`leanexegen learn record` converts an accepted proof package into an experimental knowledge package.  The package contains one worked-example entry and preserves its proof journal, accepted proof, annotations, recipes, task features, telemetry, and prior knowledge identity.  The entry carries an exact-artifact exclusion and binds every evidence file to that entry.

`leanexegen learn propose` runs a separate headless Codex task over the same evidence.  The task keeps a learning journal and produces one guidance entry, worked example, checked lemma, or checked tactic; checked Lean source receives a package namespace and passes both in-session and outer Lean builds.  The proposal remains an experimental package until an explicit promotion.

`leanexegen learn promote` copies every selected package into a self-contained forest snapshot and adds a new promoted version of the candidate package.  Promotion validates the complete resulting forest, builds every package-local Lean module in the candidate, and asks Lean to resolve every declaration advertised by its catalog.  Generation and reproof select that snapshot through `--knowledge`, while prior snapshots and candidate packages retain their original bytes.

Knowledge packages can improve later work in several ways.  A checked lemma or tactic can shorten a derivation, guidance can direct theorem selection or proof decomposition, and a worked example can show a useful proof structure.  Exact-artifact and derivative exclusions control reuse in measured tasks, while separate forests allow different package selections without editing package contents.

## Fixed-artifact evidence

Two Demo 6 runs held the formal specification, source, 1,770-byte WASM artifact, decoded program, toolchain, and checked proof kit fixed.  The first structured run found the scalar-loop, singleton-wrapper, and residual-normalization entries, rejected unrelated counter examples from their summaries, and revealed two catalog defects: declaration names were absent from index search terms, and no Euclidean-GCD guidance existed.  Its independently verified 141-line proof took 880.514 seconds, compared with the retained 510.885-second median.

The revised indexes added declaration and module aliases, and a provisional Euclidean-GCD entry recorded the invariant, measure, and arithmetic lemmas.  The second agent searched four category indexes, selected four relevant entries, opened only those entries, rejected counter, map, and filter entries from summaries, and used every selected entry in an independently verified 153-line proof.  Stage 5 took 649.557 seconds, which improved on the first structured run by 26.2 percent but remained 27.1 percent above the retained median.

These runs establish selective discovery, exclusion, related-entry use, and successful proof construction.  They do not establish lower proving time, and the current catalog is too small to measure retrieval behavior at thousands of entries.  The [Demo 6 benchmark record](../benchmarks/leanexegen/demo6-gcd42/README.md) preserves both packages, journals, accepted proofs, and telemetry.

## Growth and evaluation

Catalog growth should preserve small root files, bounded index records, canonical entry bodies, and overlapping categories.  Large categories can split into subcategories or shard JSONL indexes without changing entry identity; the root category description should tell the agent which shard to search.  Search aliases should come from declarations, modules, annotation kinds, features, and terms observed in journals rather than from copied proof prose.

Every artifact-proof iteration should review the journal, accepted proof, and telemetry together.  Journal searches reveal missing aliases, irrelevant ranking, unhelpful related links, absent abstractions, and guidance that does not match the checked theorem boundary.  Evaluation should include fixed-artifact repeats, diverse demos, held-out artifacts, and synthetic large-catalog retrieval tests.  The scorecard covers retrieval quality, files and context consulted, revisions, proof structure and size, shared abstraction use, compiler-derived evidence use, applicability, and proving time.

Promotion requires evidence appropriate to an entry's role.  A checked theorem can remain provisional after one consumer, while a worked example may remain searchable because its proof organization teaches a useful method.  Automatic selection should favor generic or recurring checked support, but file-based retrieval may retain narrow examples with exact-artifact and derivative exclusions.

The repository test places the real scalar-loop and Euclidean entries among 9,998 synthetic records in one JSONL category index.  The Demo 6 query returned only those two records and less than 10 KB of output; observed local searches completed in tens of milliseconds, although the test imposes no timing bound.  This test covers file-level selectivity rather than agent judgment, so later held-out proofs and larger real catalogs must still measure files opened, context consumed, and time before the first useful theorem application.
