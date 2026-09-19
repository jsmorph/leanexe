# Checked WGSL Compilation and Conditional GPT-2 Execution

The [technical report](main.pdf) reviews the `wgsl` branch at `ba9f02ce930243a3d35d4d10df6f9c97850ca1e8`.  It cites [Exact Execution Verification of Cached GPT-2 in Lean and WebAssembly, version 7](http://127.0.0.1:8405/abs/2609.00011v7).

## Scope

The report covers per-compilation WGSL certificates, statement execution, packed GPT-2 matrix equalities, host interfaces, controller-proof reuse, and the conditional 128-token session theorem.  It separates the branch's recorded native CPU results from fresh review checks.  Strict shader execution and host transfers are explicit premises.  Hybrid binary decoding and browser execution remain open boundaries.

The [source review](review.md) records findings and the [test record](evidence/checks.json) identifies fresh checks, including a retained certificate timeout.  The full hybrid session and native GPT-2 tests were not replayed for this report.

## Build

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdftotext main.pdf text.txt
```

Run these commands in this directory.  The compiler review harness takes a checkout path and invokes its resource-limited `tools/leanrun`.  It extracts the existing proof corpus and omits GPU execution.  Its recorded first certificate timed out under the repository's one-core limit.  The smaller Lean files in `evidence` preserve the split diagnostics.

marXiv accepted [version 4 of 2609.00012](http://127.0.0.1:8405/abs/2609.00012v4) with “No remarks.”  The archive PDF equals the reviewed submission.  The [publication record](publication.json) preserves its identity and submission history.
