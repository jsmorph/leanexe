# Exact Execution Verification of Cached GPT-2 in Lean and WebAssembly

This nine-page technical report states the checked GPT-2/128 invocation theorem, explains its arithmetic, tensor, ownership, and allocation proofs, and records the Wasmtime execution boundary and PyTorch comparisons.  It describes LeanExe source revision `f4d412b709a13bb2649fe23be267ec9928838064`.

| Material | Contents |
|----------|----------|
| [Report](main.pdf) | Reviewed PDF. |
| [LaTeX source](main.tex) | Manuscript and bibliography. |
| [Review record](review.md) | Technical and editorial review. |
| [Source identities](evidence/source-identities.json) | Cited file hashes, artifact hashes, and proof-check command. |
| [Proof-check output](evidence/proof-check.log) | Successful source-driven artifact regeneration and proof check. |
| [Submission metadata](submission-01/request.json) | Title, abstract, categories, relation, and PDF identity. |

From the repository root, build the report with two passes:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper/gpt2-verification-report paper/gpt2-verification-report/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper/gpt2-verification-report paper/gpt2-verification-report/main.tex
```

The report proves exact execution of the corresponding Lean algorithm in Talos semantics.  Its stated trust boundary includes artifact-to-model translation, the native host, and Wasmtime.  Exact-byte closure and numerical-error bounds remain deferred.
