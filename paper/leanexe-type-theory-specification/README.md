# The LeanExe Subset: Types, Extraction, and Execution

This report describes the earlier compiler at its recorded source revision.  Its reproduction commands require that revision.  [The current compiler manuals](../../README.md#documentation) describe the merged system.

The report is accepted as [marXiv:2609.00005v6](v9/pass-01/main.pdf).  It specifies runtime types and layouts, records extraction and execution through fixed implementation relations, and identifies the remaining independent formalization and refinement obligations.  The sixth archive version adds binary32 arithmetic, packed storage, current ownership rules, and per-compilation source correspondence.  Public static export is enabled in the archive and was inherited by the replacement.

| Publication file | Content |
|---|---|
| [Accepted PDF](v9/pass-01/main.pdf) | The 16-page sixth archive version, accepted without remarks. |
| [Accepted source](v9/main.tex) | LaTeX source corresponding to that PDF. |
| [PDF metadata](v9/metadata.json) | Title, authors, and abstract extracted from the PDF, with its SHA-256. |
| [Extracted text](v9/text.txt) | Text used to compare the PDF with its submission metadata. |
| [Publication record](publication-record.md) | Submission history, review results, checks, and evidence limits. |
| [Earlier source evidence](evidence/source-excerpts.md) | Declarations supporting the first report checkpoint. |
| [Source identities](evidence/source-identities-v3.json) | File digests at [a fixed source revision](https://github.com/jsmorph/leanexe/commit/df70a0a56dd909ce2a4685faba5498bdcaf01e81). |
| [Completeness review](v6/revision-notes.md) | Compiler operations, theorem scope, and remaining obligations at the report checkpoint. |
| [Editorial clarification evidence](evidence/editorial-clarifications-v2.md) | Declaration identities supporting the second version. |
| [Publication file list](publication-files.txt) | Exact repository-relative files selected for the Git checkpoint. |
| [Publication digests](publication-sha256.json) | SHA-256 values for the selected files, excluding the digest file. |

## Review history

| Archive version | Submission | Local source and PDF | Review |
|---|---|---|---|
| [v1](v4/pass-01/main.pdf) | `d75fc8acf1bc` | [Source](v4/main.tex), [PDF](v4/pass-01/main.pdf) | [Accepted with four remarks](submission-01/review.txt). |
| [v2](v5/pass-02/main.pdf) | `aca93998161c` | [Source](v5/main.tex), [PDF](v5/pass-02/main.pdf) | [Accepted with two grammar remarks](submission-02/review.txt). |
| [v3](v6/pass-01/main.pdf) | `b778e0a57bba` | [Source](v6/main.tex), [PDF](v6/pass-01/main.pdf) | [Accepted with one terminology remark](submission-03/review.txt). |
| [v4](v7/pass-01/main.pdf) | `cfc499017620` | [Source](v7/main.tex), [PDF](v7/pass-01/main.pdf) | [Accepted with two clarification remarks](submission-04/review.txt). |
| [v5](v8/pass-01/main.pdf) | `4f0f9900fbc7` | [Source](v8/main.tex), [PDF](v8/pass-01/main.pdf) | [Accepted with one callback-type remark](submission-05/review.txt). |
| [v6](v9/pass-01/main.pdf) | `268f33c99394` | [Source](v9/main.tex), [PDF](v9/pass-01/main.pdf) | [Accepted without remarks](submission-06/review.txt). |

The third version changes the terminology to “subset,” updates the report to the fixed September 18 source checkpoint, and addresses both grammar remarks from version 2.  Later revisions identify Talos and the report command’s result, distinguish allocation containment from lifetime, and distinguish a map callback’s result type from the map operation’s result type.  The sixth version is accepted without remarks.  Every submitted revision and its review remains unchanged.

## Reproduction and evidence preservation

The report uses the installed TeX Live tools and packages listed in its source.  A new build directory preserves the submitted PDFs.  From the repository root, an example rebuild is:

```sh
mkdir tmp/leanexe-type-theory-report-rebuild
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/leanexe-type-theory-report-rebuild paper/leanexe-type-theory-specification/v9/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/leanexe-type-theory-report-rebuild paper/leanexe-type-theory-specification/v9/main.tex
pdftotext tmp/leanexe-type-theory-report-rebuild/main.pdf -
```

The build path is an example fresh directory.  The original PDF embeds its build date, so a later build can differ in bytes while retaining the same text.  The final submitted build log has no warnings, undefined references, or overfull boxes.  The initial failed build log records the scalable-font requirement that led to the existing Latin Modern package.

Every submitted source and PDF, editorial record, and saved source-evidence record remains preserved.  The publication file list selects sources, submitted PDFs, final reviews, metadata, source evidence, build results, and relevant failures.  Intermediate PDFs, repeated auxiliary files, previews, duplicate downloaded PDFs, and pending-review captures remain local.  Raw logs, HTTP headers, HTML records, policy snapshots, extracted text, and review text retain their original whitespace and line endings.
