# Exact-artifact verification paper

This directory contains the research-paper draft on LeanExe's exact-artifact WebAssembly verification and proof-generation system.  The manuscript describes the implemented theorem boundary, architecture, evaluation, trust assumptions, related systems, and roadmap.  The PDF records the 7 August 2026 repository snapshot identified in the reproduction appendix.

The directory contains four publication files:

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
