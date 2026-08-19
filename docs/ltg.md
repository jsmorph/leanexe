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

Each artifact-proof workspace contains `KNOWLEDGE/forest.json`, selected package directories, `KNOWLEDGE_TASK.json`, and `KNOWLEDGE_USE.json`.  The prompt directs the agent to inspect the forest, search likely package indexes with `rg`, inspect summaries before opening entry bodies, and follow `relatedEntries` only when the proof state supports the relation.  The journal records exact queries and reasoning, while `KNOWLEDGE_USE.json` records one used or rejected result and reason for each entry the agent inspected.

```text
rg -n 'scalar-post-test|postTestProgram_spec|gcd|remainder' \
  KNOWLEDGE/packages/leanexe-core/catalog/categories
sed -n '1,220p' \
  KNOWLEDGE/packages/leanexe-core/catalog/entries/scalar-post-test-loop/entry.json
sed -n '1,240p' \
  KNOWLEDGE/packages/leanexe-core/catalog/entries/euclidean-gcd-loop/README.md
```

This protocol keeps forest size separate from prompt size.  The agent initially receives a short retrieval instruction, the forest and package manifests, and access to the file tree.  Searchable JSONL records support local filtering before the agent spends context on a full entry.

`KNOWLEDGE_TASK.json` binds the visible forest view to the task.  It records each package's identity, version, maturity, dependencies, included and excluded entries, required Lean modules, package digest, and the digest over the complete visible forest.  Exact-artifact filtering removes an excluded entry together with its bound evidence and unreferenced package-local Lean sources.  After outer proof acceptance, the proof package records the agent's final use decisions as `knowledge-evaluation.json`, together with the task digest, proof digest, source size, line count, and Stage 5 time.

The orchestrator supplies the artifact digest and selected forest to every current proof run.  Current entry schema four and knowledge-task schema two use exact artifact digests.  Validation retains older entry and task schemas containing derivative-group fields so existing proof packages remain readable, but current forest selection does not claim derivative classification.

## Validation and package identity

Catalog checks reject malformed metadata, unsupported imports, unknown categories or related entries, stale generated indexes, and stale Lean declaration checks.  Forest checks add package identity, dependency, global entry identity, package-local module namespace, source import, evidence binding, and complete file-set validation.  The generated `LTGCheck.lean` imports the core package's advertised proof modules and asks Lean to resolve every declaration.

```text
tools/ltg check
tools/knowledge check
node test/ltg.js
node test/knowledge.js
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck
```

Schema-nine proof packages archive the exact filtered forest under `knowledge/`, its manifest as `knowledge-task.json`, and the accepted knowledge evaluation.  Package validation recomputes forest and package digests, checks package and category references, validates included entries and sources, and rejects excluded entry bodies or evidence.  Schema-eight packages retain the same forest archive without an evaluation, while schema-seven packages retain their single-catalog `ltg/` archive and validator.

The checked `Behavior.lean` theorem remains the authority for verification.  Knowledge metadata and prose discharge no proof obligations, while package manifests grant import authority only to archived package-local sources whose paths, imports, and digests pass validation.  Lean checks those sources and the final proof, generated region equalities connect compiler motifs to exact decoded instructions, and the package verifier rebuilds the artifact theorem.

## Stateful learning

Stateful learning turns completed proof work into explicit input artifacts for later work.  An accepted proof package can produce an experimental knowledge package, and promotion can add that package to a self-contained forest snapshot.  A later generation or reproof selects the snapshot by path and archives its filtered contents in the resulting proof package.

| Operation | Produced artifact | Use in subsequent work |
|-----------|-------------------|------------------------|
| Proof generation or reproof | Accepted schema-nine proof package | Supplies the checked proof, journal, annotations, task features, recipes, telemetry, knowledge evaluation, and prior knowledge identity. |
| `learn record` | Experimental worked-example package | Preserves the run for retrieval, comparison, and later analysis. |
| `learn propose` | Experimental candidate package or no-entry assessment | Distills one useful entry from the run, or preserves the journaled conclusion that existing support covers the observed boundaries. |
| Review and `learn promote` | Promoted package inside a new forest snapshot | Makes the selected candidate available to later runs through `--knowledge`. |
| Later generation or reproof | New proof package | Records which promoted packages and filtered entries were available and which checked modules the proof used. |

`leanexegen learn record` converts an accepted proof package into an experimental knowledge package.  The package contains one worked-example entry and preserves its proof journal, accepted proof, frozen Talos program, generated annotation theorems, annotations, recipes, task features, telemetry, and prior knowledge identity.  A generated attempt identity distinguishes repeated records over the same accepted proof, while the entry's exact-artifact exclusion withholds the example from its source artifact.

`leanexegen learn propose` runs a separate headless Codex task over the same evidence.  The task sees the exact generated artifact adapters and may import package-local Lean modules from the archived forest, allowing later knowledge to compose earlier checked knowledge.  A checked candidate records the packages that own its direct imports, while a no-entry result preserves its proposal identity, structured decision, and learning journal without creating a package.

`leanexegen learn promote` copies every selected package into a self-contained forest snapshot and adds a new promoted version of the candidate package.  Promotion validates the resulting forest, builds every package-local Lean module, resolves every advertised declaration, and audits the printed axiom set in the same Lean check.  Generation and reproof select that snapshot through `--knowledge`, while prior snapshots and candidate packages retain their original bytes.

Knowledge packages can improve later work in several ways.  A checked lemma or tactic can shorten a derivation, guidance can direct theorem selection or proof decomposition, and a worked example can show a useful proof structure.  Exact-artifact exclusions control reuse in measured tasks, while separate forests compose different package selections without editing package contents.

The live proof task exposes selected catalogs and checked package-local Lean sources.  It omits package evidence, including accepted proofs and journals, so a broad search cannot disclose proof text outside the structured entry selected for retrieval.  The published proof package archives the complete filtered knowledge task, preserving that evidence for review and later learning work.

## Fixed-artifact evidence

Two Demo 6 runs held the formal specification, source, 1,770-byte WASM artifact, decoded program, toolchain, and checked proof kit fixed.  The first structured run found the scalar-loop, singleton-wrapper, and residual-normalization entries, rejected unrelated counter examples from their summaries, and revealed two catalog defects: declaration names were absent from index search terms, and no Euclidean-GCD guidance existed.  Its independently verified 141-line proof took 880.514 seconds, compared with the retained 510.885-second median.

The revised indexes added declaration and module aliases, and a provisional Euclidean-GCD entry recorded the invariant, measure, and arithmetic lemmas.  The second agent searched four category indexes, selected four relevant entries, opened only those entries, rejected counter, map, and filter entries from summaries, and used every selected entry in an independently verified 153-line proof.  Stage 5 took 649.557 seconds, which improved on the first structured run by 26.2 percent but remained 27.1 percent above the retained median.

These runs establish selective discovery, exclusion, related-entry use, and successful proof construction.  They do not establish lower proving time, and the current catalog is too small to measure retrieval behavior at thousands of entries.  The [Demo 6 benchmark record](../benchmarks/leanexegen/demo6-gcd42/README.md) preserves both packages, journals, accepted proofs, and telemetry.

## Growth and evaluation

Catalog growth should preserve small root files, bounded index records, canonical entry bodies, and overlapping categories.  Large categories can split into subcategories or shard JSONL indexes without changing entry identity; the root category description should tell the agent which shard to search.  Search aliases should come from declarations, modules, annotation kinds, features, and terms observed in journals rather than from copied proof prose.

Every artifact-proof iteration should review the journal, accepted proof, knowledge evaluation, and telemetry together.  The evaluation identifies which inspected entries the agent used or rejected and records each reason, while the journal retains the proof-state details behind those decisions.  Fixed-artifact repeats, diverse demos, held-out artifacts, and synthetic large-catalog retrieval tests remain useful comparisons.  The scorecard covers retrieval quality, proof structure and size, shared abstraction use, compiler-derived evidence use, applicability, and proving time.

Promotion requires evidence appropriate to an entry's role.  A checked theorem can remain provisional after one consumer, while a worked example may remain searchable because its proof organization teaches a useful method.  File-based retrieval may retain narrow examples with exact-artifact exclusions, while explicit forest composition controls which packages a proof task receives.

The repository test places the real scalar-loop and Euclidean entries among 9,998 synthetic records in one JSONL category index.  The Demo 6 query returned only those two records and less than 10 KB of output; observed local searches completed in tens of milliseconds, although the test imposes no timing bound.  This test covers file-level selectivity rather than agent judgment, so later held-out proofs and larger real catalogs must still measure files opened, context consumed, and time before the first useful theorem application.

## Stateful learning evidence

A live learning pass over Demo 11 proposed a checked theorem that composes existing result-frame getters with the generic singleton-result suffix.  Promotion created an isolated two-package forest containing twenty-five entries and one package-local Lean module.  Exact-artifact filtering withheld the theorem from Demo 11 and supplied it to the different Demo 9 sum-fold artifact.

The Demo 9 proving agent inspected the learned theorem and rejected it because the compiler recipe supplied a stronger exact singleton-result adapter.  Its accepted schema-nine package records that rejection and eleven used core entries, binding each decision to the selected forest, accepted proof, 650-line source, and 1,638.250-second Stage 5 measurement.  Independent verification accepted the complete package and rebuilt the exact artifact theorem.

The subsequent proposal task read the accepted proof, journal, telemetry, archived forest, and knowledge evaluation.  It rejected new setup and iteration lemmas because the former depended on the generated frame layout and the latter duplicated `FixedArrayFoldBody.continuingGuardedProgram_spec`, then retained the accepted composition as a benchmark-local worked example.  This result demonstrates that evaluation evidence informs the next learning pass while preserving specific proof organization separately from checked general support.

A fresh Demo 10 reproof selected that Demo 9 worked example for a wrapping-product artifact and recorded it as used for the shared branch and fold organization.  Independent package verification accepted the 571-line proof after 1,454.473 seconds of Stage 5, compared with 684 lines and 1,979.854 seconds for the preceding fixed-artifact transfer package.  The result establishes cross-artifact retrieval and use with favorable time and size measurements, while agent variation prevents attributing the measured difference to the worked example alone.

The first trial exposed a task-boundary defect because one broad search printed excerpts from the selected package's accepted-proof evidence.  The agent reported the violation, and the outer response check rejected the run despite its Lean-accepted candidate.  Live proof tasks now omit package evidence while published packages retain it, and a fresh run produced the accepted result without that exposure.

The exercise reported three representation gaps, one of which belonged to its archived input.  The current capacity and allocation entries already expose `FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail`, and the annotation generator emits the fold setup-frame equality.  Extractor version seven derives equality-node, search-key, and length-dispatch features from the checked annotation matches instead of separate instruction parsers.  The [retained exercise](../benchmarks/leanexegen/demo9-fold-sum/stateful-knowledge-1/) preserves the older proof package, proposal evidence, journals, evaluation, and follow-up candidate that produced these observations.

A later fixed-artifact Demo 9 reproof used the same archived forest, containing `leanexe-core` and `proposal-4f56fd45fe24-d4f7d73b3648`, with the generated setup-frame equality added to the recipe.  The agent retrieved and applied `function_0_array_fold_0_setup_frame_eq`, which normalized `FixedArrayFold.forwardSetupFrame` and exposed the folded loop without reducing the complete update chain.  The accepted proof used eleven entries, including the proposal package's singleton-result theorem, and independent verification accepted the exact artifact theorem.

Stage 5 took 1,780.162240 seconds, including 1,648.772899 seconds in Codex and 95.521525 seconds in outer acceptance, while the accepted source contained 543 lines, 2,320 words, and 29,074 bytes.  The result was 141.912 seconds slower and 107 lines shorter than the 1,638.250-second stateful run, and 21.075 seconds slower and 41 lines shorter than the 1,759.087-second capacity-to-allocation run.  These runs establish retrieval and use of the generated equality but do not identify its effect on proof-generation time.

Demo 12 provides the first structurally different cumulative-knowledge test after the three related fold artifacts.  The proof agent used `fixed-array-length-dispatch`, `fixed-array-capacity`, `fixed-array-allocation`, `fixed-array-map-add`, and `fixed-array-result`, adapting the map entry's checked invariant and disjoint-store pattern to two copy loops.  It rejected `fixed-array-filter-lt` because that whole-function annotation and conditional-store program did not match a dynamic search followed by a shifted copy.

The only generated annotation covered the outer upper-bound dispatch, which the recorded tactic discharged.  The five-loop interior had no annotation for the encoded `Array.findIdx?` scan or the in-bounds `Array.eraseIdx!` allocation and copy-shift region, so the accepted proof constructed both search and copy invariants locally.  Stage 5 took 3,907.231 seconds, and the independently verified proof contains 860 lines, 3,516 words, and 39,249 bytes.  These observations select general first-match and erase interfaces for development and fixed-artifact evaluation without supporting a proof-time claim yet.

The first follow-up added two provisional entries: `fixed-array-find-idx-eq` for exact execution of the compiler's one-word, literal-key scan, and `fixed-array-erase-reconstruction` for generic reconstruction from final memory reads.  Extractor version eight derives the scan's scratch position, local roles, literal key, width, and encoding from the checked `leanexe.array.find-idx-eq.v1` matcher.  A production annotation pass retained Demo 12's artifact digest and generated a Lean-checked equality to `FixedArrayFindIdxEq.program 8 0`; proof-generation evidence remains pending.

Live proposal coverage now includes a checked-theorem result and a worked-example result.  The deterministic protocol test covers the no-entry assessment, including its structured decision, source identities, and journal.  A later live run can add evidence about how often the proposer chooses that outcome.
