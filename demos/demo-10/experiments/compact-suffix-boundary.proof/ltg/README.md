# Lean Artifact-Proof LTG

This directory contains checked proof assets, annotation support, proof-generation methods, guidance, and worked examples used for artifact proofs.  Start with `categories.json`, then search the relevant `categories/<category>/tools.jsonl` files by annotation kind, feature, declaration, or summary.  Open an entry under `entries/` only after its index record appears relevant to the current goal.

Use ordinary file searches instead of reading the complete tree.  A typical search is `rg -n 'scalar-post-test|counter|singleton' LTG/categories`, followed by reading the selected `entry.json` and `README.md`.  Record the query, entries inspected, entries used, and entries rejected in `PROOF_JOURNAL.md` as the proof develops.

An entry's prose and metadata provide guidance rather than proof.  Lean checks every imported declaration, while compiler annotations and generated region equalities connect an entry to the exact decoded artifact.  Evidence status records promotion and future selection policy, and checked narrow material remains available as a worked example unless artifact-exclusion rules remove it from a measured task.

Each entry has one canonical directory and may appear in several category indexes.  `tools/ltg rebuild` derives the JSONL indexes and the Lean declaration check from `entry.json`; `tools/ltg check` rejects stale generated files or invalid references.  Category indexes therefore provide overlapping views without copying canonical entry content.
