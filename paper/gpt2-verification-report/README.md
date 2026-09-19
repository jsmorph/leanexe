# Exact Execution Verification of Cached GPT-2 in Lean and WebAssembly

This thirteen-page technical report explains the goal of source-to-artifact verification and its application to complete GPT-2 inference, then states the checked connection from the frozen GPT-2/128 binary bytes to the Lean cached-step algorithm.  It explains decoding, validation, translation, our floating-point extensions to Talos, and the arithmetic, tensor, ownership, and allocation proofs.  It records the theorem's axiom dependencies, statement-review lemmas, two open automation checks, Wasmtime execution boundary, and PyTorch comparisons.  It describes LeanExe source revision `4360920c3060d1c625b1860229b5116804d177c8`.

marXiv accepted [version 8 of 2609.00011](http://127.0.0.1:8405/abs/2609.00011v8).  The reviewer records one style remark about explaining standard logical axioms.  The report retains that brief explanation as requested.  The archive PDF matches the reviewed local PDF.

| Material | Contents |
|----------|----------|
| [Report](main.pdf) | Reviewed PDF. |
| [LaTeX source](main.tex) | Manuscript and bibliography. |
| [Review record](review.md) | Technical and editorial review. |
| [Source identities](evidence/source-identities.json) | Cited file hashes, artifact hashes, and the recorded aggregate proof result. |
| [Talos extension review](evidence/talos-fp-review.json) | Earlier evaluator, pinned arithmetic definitions, and proof sources. |
| [Proof-check output](evidence/proof-check.log) | Successful source-driven artifact regeneration and proof check. |
| [Artifact-check output](evidence/artifact-check-20260919-authorized.log.gz) | Compressed output of the successful exact-artifact package check. |
| [Statement-review output](evidence/statement-review-20260919.txt) | Seven checked corollaries and the combined theorem's axiom report. |
| [Submission metadata](submission-08/request.json) | Title and abstract extracted from the revised PDF, categories, relation, and PDF identity. |
| [Publication record](publication.json) | Accepted version, archive links, PDF identity, and submission history. |

From the repository root, build the report with two passes:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper/gpt2-verification-report paper/gpt2-verification-report/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper/gpt2-verification-report paper/gpt2-verification-report/main.tex
```

The report proves exact execution of the corresponding Lean algorithm for the decoded frozen artifact in Talos semantics.  Its stated trust boundary includes the interpretation of the formal grammar, validation, translation, and execution definitions as WebAssembly, file and byte I/O, the native host, and Wasmtime.  The review identifies the CLI's artifact-identity comparison and the combined theorem's automated three-axiom audit as open checks.  Numerical-error bounds remain deferred.
