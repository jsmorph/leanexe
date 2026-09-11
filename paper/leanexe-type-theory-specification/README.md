# The LeanExe Fragment: Types, Extraction, and Execution

The report is accepted as [marXiv:2609.00005v2](http://127.0.0.1:8405/abs/2609.00005v2).  It specifies runtime types and layouts, records extraction and execution through fixed implementation relations, and identifies the remaining independent formalization and refinement obligations.  Public static export is off.

| Publication file | Content |
|---|---|
| [Accepted PDF](v5/pass-02/main.pdf) | The 13-page second archive version. |
| [Accepted source](v5/main.tex) | LaTeX source corresponding to that PDF. |
| [PDF metadata](v5/metadata.json) | Title, authors, and abstract extracted from the PDF, with its SHA-256. |
| [Extracted text](v5/text.txt) | Text used to compare the PDF with its submission metadata. |
| [Publication record](publication-record.md) | Submission history, review results, checks, and evidence limits. |
| [Source evidence](evidence/source-excerpts.md) | Fixed-checkpoint declarations supporting the audit and theorem boundaries. |
| [Source identities](evidence/source-identities.json) | File digests and the compared implementation revisions. |
| [Editorial clarification evidence](evidence/editorial-clarifications-v2.md) | Declaration identities supporting the second version. |
| [Publication file list](publication-files.txt) | Exact repository-relative files selected for the Git checkpoint. |
| [Publication digests](publication-sha256.json) | SHA-256 values for the selected files, excluding the digest file. |

## Review history

| Archive version | Submission | Local source and PDF | Review |
|---|---|---|---|
| [v1](http://127.0.0.1:8405/abs/2609.00005v1) | `d75fc8acf1bc` | [Source](v4/main.tex), [PDF](v4/pass-01/main.pdf) | [Accepted with four remarks](submission-01/review.txt). |
| [v2](http://127.0.0.1:8405/abs/2609.00005v2) | `aca93998161c` | [Source](v5/main.tex), [PDF](v5/pass-02/main.pdf) | [Accepted with two grammar remarks](submission-02/review.txt). |

The second version addresses all four first-review remarks.  Its review requests periods in place of the semicolons joining the array-read and map/modify descriptions in Table 2.  Both submitted revisions and their full reviews remain unchanged.

## Reproduction and evidence preservation

The report uses the installed TeX Live tools and packages listed in its source.  A new build directory preserves the submitted PDFs.  From the repository root, an example rebuild is:

```sh
mkdir tmp/leanexe-type-theory-report-rebuild
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/leanexe-type-theory-report-rebuild paper/leanexe-type-theory-specification/v5/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/leanexe-type-theory-report-rebuild paper/leanexe-type-theory-specification/v5/main.tex
pdftotext tmp/leanexe-type-theory-report-rebuild/main.pdf -
```

The build path is an example fresh directory.  The original PDF embeds its build date, so a later build can differ in bytes while retaining the same text.  The final submitted build log has no warnings, undefined references, or overfull boxes.  The initial failed build log records the scalable-font requirement that led to the existing Latin Modern package.

Every local draft, build product, preview, and polling capture remains preserved.  The publication file list selects sources, submitted PDFs, final reviews, metadata, source evidence, build results, and relevant failures.  Intermediate PDFs, repeated auxiliary files, previews, duplicate downloaded PDFs, and pending-review captures remain local.  Raw logs, HTTP headers, HTML records, policy snapshots, extracted text, and review text retain their original whitespace and line endings.
