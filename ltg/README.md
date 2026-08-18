# Lean Artifact-Proof LTG

This directory is the `leanexe-core` knowledge package.  It contains checked proof assets, annotation support, proof-generation methods, guidance, and worked examples used for artifact proofs.  Start with `categories.json`, then search the relevant `categories/<category>/tools.jsonl` files by annotation kind, feature, declaration, or summary.

Use ordinary file searches before opening entry bodies.  In the repository, a typical search is `rg -n 'scalar-post-test|counter|singleton' ltg/categories`, followed by reading the selected `entry.json` and `README.md`.  In a proof task, `KNOWLEDGE/forest.json` identifies this package's task path, and the proof journal records the query, packages and entries inspected, entries used, and entries rejected.

An entry's prose and metadata provide guidance rather than proof.  Lean checks every imported declaration, while compiler annotations and generated region equalities connect an entry to the exact decoded artifact.  Evidence status records promotion and future selection policy, and checked narrow material remains available as a worked example unless artifact-exclusion rules remove it from a measured task.

Each entry has one canonical directory and may appear in several category indexes.  `tools/ltg rebuild` derives the JSONL indexes and the Lean declaration check from `entry.json`; `tools/ltg check` rejects stale generated files or invalid references.  Category indexes therefore provide overlapping views without copying canonical entry content.

Schema-2 entries may contain structured tactic records.  Each record names a command token, defining ProofKit module, goal shape, required premises, applicable annotation kinds, and fallback theorem.  Catalog validation rejects an undefined command, a module or fallback outside the entry, and an annotation kind outside the entry's declared scope.

Schema-3 entries may contain guidance or worked-example records without Lean modules or declarations.  Executable schema-3 entries still require checked modules and declarations, and structured tactics still require a checked fallback declaration.  `knowledge-package.json` supplies this catalog's package identity, version, maturity, dependencies, and package-local content inventory.
