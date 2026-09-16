# Euler report publication record

## Submitted document

The title is “A Verified WebAssembly Solver for a Two-Dimensional Euler Riemann Problem.”  The authors are Codex GPT-6 and Jamie Stephens.  The [final PDF](v6/pass-02/main.pdf) has 15 pages and two figures, including the complete 800 × 800 density and pressure PNG.  Its SHA-256 is `88d4f024626722462ea622ccda871ee8f1ec261f6c6cd42822df56b9bf0b4eba`.  The downloaded archive PDF has the same digest.

The primary subject is `cs.LO`, with `cs.PL` as the secondary subject.  The [PDF metadata](v6/metadata.json) retains the extracted title and abstract.  The report cites proof and data checkpoint `73e5b54ee6ba398cdd4d42feadc42e2c6ec5a33a`.  Public static export is off.

## Archive history

The final paper is [marXiv:2609.00006v4](http://127.0.0.1:8405/abs/2609.00006v4).  All revisions use `replaces=2609.00006` after the first accepted submission.  Times in the table are UTC.

| Submission | Manuscript | Submitted | Decision | Review |
|------------|------------|-----------|----------|--------|
| `5994a7522c90` | [First submitted PDF](v3/pass-02/main.pdf) | 15 September, 22:59:51 | Accepted, 15 September, 23:02:37 | [Three definition and redundancy remarks](submission-01/review.txt). |
| `128aa5349052` | [End-to-end expansion](v4/pass-02/main.pdf) | 15 September, 23:12:01 | Accepted, 15 September, 23:55:13 | [One minmod terminology remark](submission-02/review.txt). |
| `f0787a3ef99b` | [Minmod clarification](v5/pass-02/main.pdf) | 15 September, 23:57:04 | Accepted, 16 September, 00:01:10 | [Five prose remarks](submission-03/review.txt). |
| `661f900da98f` | [Final prose revision](v6/pass-02/main.pdf) | 16 September, 00:02:49 | Accepted, 16 September, 00:05:08 | [No remarks](submission-04/review.txt). |

The first revision defines binary64 state and grid safety, expands LTG, removes a repeated figure sentence, and adds the explicit end-to-end proof composition requested by the user.  The next revision specifies minmod reconstruction with factor 1/2 before positivity limiting.  The final revision states the counterexample findings in the abstract, names the first section's result and the actors who performed the reported work, and removes a redundant sentence.  The end-to-end section and both figures are unchanged in these last two revisions.

A sandboxed connection attempt failed before reaching the archive.  Direct curl uploads then returned HTTP 303.  The local submission directories preserve the request and response records, complete reviews, and downloaded PDF checks.  The [review record](review.md) documents the technical, prose, PDF, and data checks.  The [publication file list](publication-files.json) bounds the repository checkpoint.
