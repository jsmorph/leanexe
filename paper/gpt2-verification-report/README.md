# Exact Execution Verification of Cached GPT-2 in Lean and WebAssembly

This ten-page technical report states the checked GPT-2/128 invocation theorem, explains our floating-point extensions to Talos and the arithmetic, tensor, ownership, and allocation proofs, and records the Wasmtime execution boundary and PyTorch comparisons.  It describes LeanExe source revision `f4d412b709a13bb2649fe23be267ec9928838064`.

marXiv accepted [version 5 of 2609.00011](http://127.0.0.1:8405/abs/2609.00011v5) with no remarks.  This version adds the Talos floating-point extension account and defines Talos and Wasmtime at first use in the abstract and body.

| Material | Contents |
|----------|----------|
| [Report](main.pdf) | Reviewed PDF. |
| [LaTeX source](main.tex) | Manuscript and bibliography. |
| [Review record](review.md) | Technical and editorial review. |
| [Source identities](evidence/source-identities.json) | Cited file hashes, artifact hashes, and proof-check command. |
| [Talos extension review](evidence/talos-fp-review.json) | Earlier evaluator, pinned arithmetic definitions, and proof sources. |
| [Proof-check output](evidence/proof-check.log) | Successful source-driven artifact regeneration and proof check. |
| [Submission metadata](submission-05/request.json) | Title, abstract, categories, relation, and revised PDF identity. |
| [Publication record](publication.json) | Accepted version, archive links, PDF identity, and submission history. |

From the repository root, build the report with two passes:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper/gpt2-verification-report paper/gpt2-verification-report/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper/gpt2-verification-report paper/gpt2-verification-report/main.tex
```

The report proves exact execution of the corresponding Lean algorithm in Talos semantics.  Its stated trust boundary includes artifact-to-model translation, the native host, and Wasmtime.  Exact-byte closure and numerical-error bounds remain deferred.
