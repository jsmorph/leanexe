# GPT-2 inference from Lean to WebAssembly and WGSL

The 42-page [standalone technical report](main.pdf) covers LeanExe's compilation and verification method, the complete CPU GPT-2 artifact theorem, the WGSL kernel and conditional hybrid proofs, the proof structure, native execution records, browser comparison images, and related verification research.  Publication status: accepted as [marXiv:2609.00014v1](http://127.0.0.1:8405/abs/2609.00014v1).

The [publication record](publication.json) identifies the accepted version.  The archived PDF equals the submitted and local PDFs.  The [editorial review](submission-01/editorial-review.md) records nine style remarks.

The CPU proof checkpoint is `4360920c3060d1c625b1860229b5116804d177c8`.  The WGSL and browser source checkpoint is `9c7c7898ecae5f636cf1047142c8a68c1936e041`.  The [source identities](evidence/cited-sources.json) identify the cited files.  The [review record](review.md) distinguishes prior checked proofs, recorded runs, supplied images, and document checks.

The [literature-search record](evidence/literature-search.md) preserves the sources and comparison criteria.  The two original browser images are in `figures`, with their [identities and provenance](evidence/images.json).  The text describes the screenshot observations and the corresponding timing and memory definitions in the browser source.

The [document record](evidence/document.json) identifies the reviewed PDF and its document checks.  The report has 78 bibliography entries, six tables, and three figures.

## Build

Run these commands in this report directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdftotext -layout main.pdf evidence/text-layout.txt
```

The manuscript uses separate section files and two included bibliography files.  The earlier CPU and WGSL reports remain in their own directories with their publication records.
