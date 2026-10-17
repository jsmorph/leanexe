# LeanExe research papers

These papers describe repository revisions from August and September 2026.  Their APIs, binaries, theorem statements, and reproduction commands belong to those revisions.  Each report preserves its source, PDF, and evidence.  The current system has separate manuals for [the LeanExe compiler](../docs/leanexe-manual.md) and [the verified compiler](../docs/verified-manual.md), with the current numerical results in [the numerical index](../index.md).

| Work | Subject | Record |
|------|---------|--------|
| [Exact-artifact verification paper](main.pdf) | Complete system, evaluation, trusted base, and roadmap. | Root LaTeX source and review record. |
| [Structured LTG note](structured-ltg-note/README.md) | Selective retrieval from the growing proof knowledge base. | [marXiv:2608.00029](structured-ltg-note/main.pdf) |
| [Frame-accessor note](frame-accessor-note/README.md) | Compiler-generated frame projections and their proof screens. | [marXiv:2608.00034](frame-accessor-note/main.pdf) |
| [Tactic-retrieval note](tactic-retrieval-note/README.md) | Goal-shape tactic indexing, selection, and accepted proof evidence. | [marXiv:2608.00036](tactic-retrieval-note/main.pdf) |
| [The LeanExe Subset](leanexe-type-theory-specification/README.md) | Runtime typing, extraction, packed storage, and per-compilation proof obligations. | [marXiv:2609.00005](leanexe-type-theory-specification/v9/pass-01/main.pdf) |
| [Reconstructed Euler report](euler-reconstructed-report/README.md) | Exact-binary solver proof, physical numerical guarantees, and 192-grid and 800-grid results. | [marXiv:2609.00006](euler-reconstructed-report/v6/pass-02/main.pdf) |
| [Cached GPT-2 verification report](gpt2-verification-report/README.md) | Exact execution of the Lean GPT-2/128 recurrence, packed FP32 arithmetic, allocation sufficiency, and command-line inference. | [marXiv:2609.00011](gpt2-verification-report/main.pdf) |
| [WGSL verification report](wgsl-verification-report/README.md) | Checked shader compilation, packed matrix equalities, and conditional hybrid GPT-2/128 execution. | [marXiv:2609.00012](wgsl-verification-report/main.pdf) |
| [Comprehensive GPT-2 report](gpt2-comprehensive-report/README.md) | LeanExe, CPU artifact and WGSL proofs, theorem structure, literature comparison, and browser execution images. | [marXiv:2609.00014](gpt2-comprehensive-report/main.pdf) |
| [Quantized GPT-2 report](gpt2-quantized-report/README.md) | Grouped INT8 arithmetic, exact binary and cached-session proofs, accuracy diagnosis, runtime measurements, and numerical bounds. | [marXiv:2609.00018](gpt2-quantized-report/main.pdf) |
| [Drone verification report](drone-verification-report/README.md) | Finite-graph optimality, continuous flight safety, generated-model execution, and five terrain runs. | [marXiv:2609.00019](drone-verification-report/main.pdf) |

The root manuscript consists of four publication files:

- [Manuscript source](main.tex): the complete LaTeX document.
- [Bibliography](references.bib): thirty-two cited primary papers, specifications, and software records.
- [Rendered paper](main.pdf): the generated eighteen-page PDF.
- [Review record](review-notes.md): the technical, editorial, and acceptance review passes applied before the final build.

Build the document by running the commands below from this directory.  The first LaTeX pass creates the citation inventory, BibTeX generates the bibliography, and the final two LaTeX passes resolve citations, references, and PDF outlines.  A clean build has no undefined citation, undefined reference, overfull-box, or BibTeX warnings.

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The anonymous author field and generic article class are placeholders.  An arXiv submission needs the author list, affiliations, subject classification, license selection, and the final immutable LeanExe release identifier.  The final release record also needs a matching cold-checkout receipt for the revision that contains every reported result.
