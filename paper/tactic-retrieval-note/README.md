# Goal-Shape Tactic Retrieval for Exact WebAssembly Artifact Proofs

This report describes the earlier compiler at its recorded source revision.  Its reproduction commands require that revision.  [The current compiler manuals](../../README.md#documentation) describe the merged system.

This directory contains the source, bibliography, reviewed PDF, and review record for the tactic-retrieval report.  marXiv published the paper as [marXiv:2608.00036](main.pdf) under Logic in Computer Science with an Artificial Intelligence cross-list.  Submission `a591d0435805` established the first accepted version, and replacement `f0bbd4d70321` addressed all eleven remarks and was accepted with no remarks.

The [LaTeX source](main.tex) states the experiment, result, and limitations.  The [bibliography](references.bib) records the Lean, theorem-proving, WebAssembly-verification, and verified-compilation sources used by the report.  The [review record](review-notes.md) binds the claims to repository evidence, records the prose and rendered-document checks, and maps every first-round remark to its replacement edit.

The checked [PDF](main.pdf) was built with `pdflatex`, `bibtex`, and two final `pdflatex` passes.  A later source edit that does not change citations needs enough `pdflatex` passes to clear the rerun warning and stabilize references.  The final build log contained no undefined references, missing citations, overfull boxes, or underfull boxes.

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
