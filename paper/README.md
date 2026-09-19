# LeanExe research papers

This directory contains the main research paper, seven focused reports, and a comprehensive GPT-2 draft covering LeanExe's language, WebAssembly and shader verification, numerical computation, and proof-generation system.  The main manuscript describes the implemented theorem boundary, architecture, evaluation, trust assumptions, related systems, and roadmap.  Each report retains its source, references, and PDF in a separate directory, with publication records for accepted reports.

| Work | Subject | Record |
|------|---------|--------|
| [Exact-artifact verification paper](main.pdf) | Complete system, evaluation, trusted base, and roadmap. | Root LaTeX source and review record. |
| [Structured LTG note](structured-ltg-note/README.md) | Selective retrieval from the growing proof knowledge base. | [marXiv:2608.00029](http://localhost:8000/abs/2608.00029) |
| [Frame-accessor note](frame-accessor-note/README.md) | Compiler-generated frame projections and their proof screens. | [marXiv:2608.00034](http://localhost:8000/abs/2608.00034) |
| [Tactic-retrieval note](tactic-retrieval-note/README.md) | Goal-shape tactic indexing, selection, and accepted proof evidence. | [marXiv:2608.00036](http://localhost:8000/abs/2608.00036) |
| [The LeanExe Subset](leanexe-type-theory-specification/README.md) | Runtime typing, extraction, packed storage, and per-compilation proof obligations. | [marXiv:2609.00005](http://127.0.0.1:8405/abs/2609.00005) |
| [Reconstructed Euler report](euler-reconstructed-report/README.md) | Exact-binary solver proof, physical numerical guarantees, and 192-grid and 800-grid results. | [marXiv:2609.00006](http://127.0.0.1:8405/abs/2609.00006) |
| [Cached GPT-2 verification report](gpt2-verification-report/README.md) | Exact execution of the Lean GPT-2/128 recurrence, packed FP32 arithmetic, allocation sufficiency, and command-line inference. | [marXiv:2609.00011](http://127.0.0.1:8405/abs/2609.00011) |
| [WGSL verification report](wgsl-verification-report/README.md) | Checked shader compilation, packed matrix equalities, and conditional hybrid GPT-2/128 execution. | [marXiv:2609.00012](http://127.0.0.1:8405/abs/2609.00012) |
| [Comprehensive GPT-2 report](gpt2-comprehensive-report/README.md) | LeanExe, CPU artifact and WGSL proofs, theorem structure, literature comparison, and browser execution images. | Standalone draft for marXiv. |

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
