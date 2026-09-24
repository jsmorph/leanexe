# Quantized GPT-2 inference report

The [twenty-page report](main.pdf) describes LeanExe's grouped INT8 GPT-2 implementation, exact WebAssembly/session proofs, checkpoint correspondence, retained accuracy and timing experiments, conditional numerical bounds, and observed-logit certificates.  It fixes source revision `c655d35b5011c1703dfd22bcceaec4e5bee17088` and the 28,315-byte binary with SHA-256 `9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075`.

The manuscript distinguishes the completed quantized component from unfinished repository-wide release checks.  It reports zero forward-bound token certificates and 232 common-offset certificates derived from observed logit pairs.  Jamie Stephens, Morphism, is the author.  marXiv accepted [version two](http://127.0.0.1:8405/abs/2609.00018v2) on 24 September 2026 with no remarks.

## Manuscript and evidence

The [LaTeX manuscript](main.tex) includes nine section files and the [bibliography](references.bib).  The [review record](review-notes.md), [independent first-version review](independent-review.md), and [independent revision review](independent-review-v2.md) describe the technical and editorial passes.  The [build result](evidence/build-result.json) records PDF identity and validation results.  The [extracted text](evidence/pdf-text.txt), [submission metadata](evidence/metadata.json), and [computed evidence summary](evidence/summary.json) support final review.

The [publication record](publication.json) identifies both accepted submissions.  Version one's [archive review](submission-01/review.txt) requested an exponent definition and two presentation edits.  Version two addresses all three remarks.  Its [final archive review](submission-02/review.txt) has no remarks.  The [preserved first version](v1/main.pdf) retains its source and metadata.  Both downloaded archive PDFs match their submitted hashes.

The [evidence inventory](evidence/inventory.json) contains 67 file identities at the cited source revision.  The checker reads those committed objects, so unrelated working-tree edits do not change the report's input set.  Run it from the repository root:

```sh
python3 paper/gpt2-quantized-report/check-evidence.py
```

The current archive [acceptance requirements](evidence/marxiv-standards.md) and [style manual](evidence/marxiv-style.md) were fetched and read before drafting.  The [cited-source record](evidence/cited-sources.json) identifies the primary literature used.

## PDF build

The build uses the installed pdfLaTeX, BibTeX, and Poppler tools.  From this report directory, create a temporary output directory and run:

```sh
mkdir -p /tmp/leanexe-quantized-report-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/leanexe-quantized-report-build main.tex
```

Run BibTeX from the temporary output directory, with the report directory in `BIBINPUTS`:

```sh
cd /tmp/leanexe-quantized-report-build
env BIBINPUTS=/home/somebody/src/leanexe/paper/gpt2-quantized-report: bibtex main
```

Return to the report directory, then resolve references and copy the PDF:

```sh
cd /home/somebody/src/leanexe/paper/gpt2-quantized-report
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/leanexe-quantized-report-build main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/leanexe-quantized-report-build main.tex
cp /tmp/leanexe-quantized-report-build/main.pdf main.pdf
pdftotext main.pdf evidence/pdf-text.txt
```

The final build has no undefined citations or references, overfull boxes, or BibTeX warnings.  Three underfull-paragraph diagnostics remain.  The PDF has extractable text and preserves ASCII double hyphens in command options.  Temporary LaTeX intermediates remain under `/tmp`.

## Component reproduction

From the repository root, the exact-binary package check is:

```sh
tools/artifact-proof.js check proofs/artifacts/gpt2_quantized_cached/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/program.wasm Project.Gpt2QuantizedCached.ArtifactTranslation
```

The source-driven check is:

```sh
tools/talos-proof.js check gpt2_quantized_cached
```

The [evaluation guide](../../data/gpt2-quantized-v1/README.md) records the checkpoint export, independent reference tests, completion comparison, scoped benchmark, capture, and native checker commands.  Each recorded check identifies its inputs and trust boundary.  This report's drafting and review did not rerun Lean, model evaluation, or benchmarks.
