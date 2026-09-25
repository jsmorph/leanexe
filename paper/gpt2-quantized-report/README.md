# Quantized GPT-2 inference report

The [twenty-page report](main.pdf) describes LeanExe's grouped INT8 GPT-2 implementation, exact WebAssembly/session proofs, checkpoint correspondence, retained accuracy and timing experiments, conditional numerical bounds, and observed-logit certificates.  It fixes source revision `c655d35b5011c1703dfd22bcceaec4e5bee17088` and the 28,315-byte binary with SHA-256 `9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075`.

At its cited source revision, the manuscript distinguishes the completed quantized component from unfinished repository-wide checks.  The [development status](../../docs/status.md) records subsequent verification.  The report records zero forward-bound token certificates and 232 common-offset certificates derived from observed logit pairs.  Jamie Stephens, Morphism, is the author.  marXiv accepted [version two](http://127.0.0.1:8405/abs/2609.00018v2) on 24 September 2026 with no remarks.

## Manuscript and evidence

The [LaTeX manuscript](main.tex) includes nine section files and the [bibliography](references.bib).  The [review record](review-notes.md), [independent first-version review](independent-review.md), and [independent revision review](independent-review-v2.md) describe the technical and editorial passes.  The [build result](evidence/build-result.json) records PDF identity and validation results.  The [extracted text](evidence/pdf-text.txt), [submission metadata](evidence/metadata.json), and [computed evidence summary](evidence/summary.json) support final review.

The [publication record](publication.json) identifies both accepted submissions.  Version one's [archive review](submission-01/review.txt) requested an exponent definition and two presentation edits.  Version two addresses all three remarks.  Its [final archive review](submission-02/review.txt) has no remarks.  The [preserved first version](v1/main.pdf) retains its source and metadata.  Both downloaded archive PDFs match their submitted hashes.

The [evidence inventory](evidence/inventory.json) contains 67 file identities at the cited source revision.  The checker reads those committed objects, so unrelated working-tree edits do not change the report's input set.  Run it from the repository root:

```sh
python3 paper/gpt2-quantized-report/check-evidence.py
```

The current archive [acceptance requirements](evidence/marxiv-standards.md) and [style manual](evidence/marxiv-style.md) were fetched and read before drafting.  The [cited-source record](evidence/cited-sources.json) identifies the primary literature used.

## PDF build

The build uses the installed pdfLaTeX, BibTeX, and Poppler tools.  From the repository root:

```sh
report_dir="$PWD/paper/gpt2-quantized-report"
report_build_dir="$PWD/build/gpt2-quantized-report"
mkdir -p "$report_build_dir"
cd "$report_dir"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$report_build_dir" main.tex
cd "$report_build_dir"
env BIBINPUTS="$report_dir:" bibtex main
cd "$report_dir"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$report_build_dir" main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$report_build_dir" main.tex
cp "$report_build_dir/main.pdf" main.pdf
pdftotext main.pdf evidence/pdf-text.txt
```

The final build has no undefined citations or references, overfull boxes, or BibTeX warnings.  Three underfull-paragraph diagnostics remain.  The PDF has extractable text and preserves ASCII double hyphens in command options.  These commands place LaTeX intermediates in the ignored repository build directory.

## Component reproduction

These commands check the current implementation from the repository root.  The report's binary and proof belong to the source revision stated above.  The current exact-binary package check is:

```sh
tools/artifact-proof.js check proofs/artifacts/gpt2_quantized_cached/87026cf4bd73cc7ae793195ccc1a6e0469d2eb3d007d1e01cad676e551176aa8/program.wasm Project.Gpt2QuantizedCached.ArtifactTranslation
```

The source-driven check is:

```sh
tools/talos-proof.js check gpt2_quantized_cached
```

The [evaluation guide](../../data/gpt2-quantized-v1/README.md) records the checkpoint export, independent reference tests, completion comparison, scoped benchmark, capture, and native checker commands.  Each recorded check identifies its inputs and trust boundary.  This report's drafting and review did not rerun Lean, model evaluation, or benchmarks.
