# Exact-artifact verification paper

This directory contains the main research paper and three focused research notes on LeanExe's exact-artifact WebAssembly verification and proof-generation system.  The main manuscript describes the implemented theorem boundary, architecture, evaluation, trust assumptions, related systems, and roadmap.  Each note retains its source, bibliography, reviewed PDF, and publication record in a separate directory.

| Work | Subject | Record |
|------|---------|--------|
| [Exact-artifact verification paper](main.pdf) | Complete system, evaluation, trusted base, and roadmap. | Root LaTeX source and review record. |
| [Structured LTG note](structured-ltg-note/README.md) | Selective retrieval from the growing proof knowledge base. | [marXiv:2608.00029](http://localhost:8000/abs/2608.00029) |
| [Frame-accessor note](frame-accessor-note/README.md) | Compiler-generated frame projections and their proof screens. | [marXiv:2608.00034](http://localhost:8000/abs/2608.00034) |
| [Tactic-retrieval note](tactic-retrieval-note/README.md) | Goal-shape tactic indexing, selection, and accepted proof evidence. | [marXiv:2608.00036](http://localhost:8000/abs/2608.00036) |

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
