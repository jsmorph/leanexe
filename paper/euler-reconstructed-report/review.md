# Euler report review

## Evidence and scope

The report uses the completed proof and data checkpoint `73e5b54ee6ba398cdd4d42feadc42e2c6ec5a33a`.  Preparation read the live marXiv standards and style manual before drafting.  The archive is available at port 8405.  The optional skill-linked user guide was absent at its resolved path.  The skill and live submission form supply the submission procedure.

The technical review checks the source definitions of the four complete solver specifications, exact-byte transfer, initial reset, reconstruction, physical trace balance, time control, and final output.  The figures and reported measurements come from the preserved production directories.  The report does not rerun the solver or claim a new proof measurement.

## Review checklist

- [x] Read the acceptance standards and style manual before drafting.
- [x] Inspect the source theorem statements and production summaries.
- [x] Verify the Lanyon comparison against its pinned proof source.
- [x] Complete the first substantive review against the source definitions.
- [x] Complete the second technical and prose review.
- [x] Compile and inspect every PDF page, references, and extracted text.
- [x] Compare submission metadata with the compiled PDF.
- [x] Submit the first version and retain the complete editorial decision.
- [x] Address all three editorial remarks and expand end-to-end proof coverage.
- [x] Retain the second version's editorial decision and address its terminology remark.
- [x] Retain the third version's editorial decision and address its five prose remarks.
- [x] Retain the final prose revision's editorial decision: accepted, no remarks.

## Technical and prose review

The first review checked the exact final-time word, supported input bounds, common-factor trial sequence, local error certificate, eigenvector determinant, physical trace residual, allocator budget, and startup-reset premise against the named Lean definitions.  Both counterexamples agree with their real and binary64 declarations.  The second draft distinguishes output pressure from physical real pressure and states the published minmod reconstruction's fixed factor and lack of a face-admissibility test in those definitions.

The second review checked the extracted body and source for unsupported claims, missing hypotheses, filler, repetitive framing, and ambiguous notation.  The third draft assigns conservation to the accepted trace explicitly and describes the repeated eigenvalue's two independent vectors.  It retains the finite grid bound, conditional success claim, sampled memory qualification, source-specific Lanyon comparison, and absence of a continuous convergence or measured global residual result.  Compiler annotations and LTG use receive a source-backed account without a held-out speedup claim.

The first build succeeded with expected first-pass unresolved references and three overfull boxes in the theorem index.  The second and third drafts fix those boxes.  Their second passes have no warnings, undefined references, overfull boxes, or underfull boxes.  A source-link check first mistook a macro parameter for a concrete path.  Excluding that parameter made all 44 concrete linked files pass.  The repository documentation check passes with the report and preserved policy copies.

## PDF and data review

Rendered and viewed all 14 pages of the third draft at 1200 pixels.  Equations, table continuations, references, page numbers, and captions are legible and unclipped.  Page 9 contains the 192-grid image and results table.  Page 10 contains the required 800-grid image.  Both figures retain the production PNG content and display readable axes and color bars.

Verified the frozen binary SHA-256 and both word-file lengths, headers, and SHA-256 values against the production summaries.  The [initial identity record](evidence/source-identities.json) records cited files and production inputs.  The title and abstract were extracted from the final PDF.  The abstract matches the source after whitespace and typographic-apostrophe normalization, with exact extracted wording retained in the request.  Authors match the PDF.  The metadata records the submitted PDF digest.

## Submission

The first upload used a Python subprocess in the sandbox and could not connect to the archive.  Its error handler then attempted to read a response file that curl had not created.  The failed result remains preserved.  A direct authorized curl invocation outside that sandbox returned HTTP 303 with submission identifier `5994a7522c90`.  The status page confirms that editorial review started.  There was one accepted upload and no duplicate submission.

## Editorial revision and end-to-end review

marXiv accepted the first submission as 2609.00006.  The [complete review](submission-01/review.txt) requested definitions of binary64 state and grid safety, expansion of LTG, and deletion of a repeated figure sentence.  The fourth manuscript addresses all three remarks.

The user requested careful end-to-end coverage.  Section 5.2 now expands the byte-decoding and validation equalities, execution-model transfer, quantified total-correctness predicate, and exact array postcondition.  The review checked these against the pinned Talos definition and the artifact, control, trace, and output modules.  It checked the distinction between interpreter success and application status zero, the output's relation to the complete internal grid, and the runtime assumptions for the observed production runs and images.

Both fourth-draft LaTeX passes succeeded.  The 15-page second pass has no warnings, undefined references, overfull boxes, or underfull boxes.  Every page passed visual review at 1000 pixels, including the new equations and the original 800-grid image on page 11.  The extracted title and abstract match the submitted metadata.  The archive received the revision as submission `128aa5349052` with `replaces=2609.00006`.

A check of all 50 fourth-draft source digests against their cited Git objects found one provenance-record error: the journal digest came from the working copy.  The other 49 digests matched.  The [final identity record](evidence/final-source-identities.json) uses the cited checkpoint's journal and preserves the correction.  The manuscript already cites that checkpoint.  The earlier records remain available for the review history.

## Final terminology review

The second submission was accepted with one remark: “Unlimited minmod reconstruction” leaves the operation ambiguous because it already applies minmod.  The fifth manuscript changes only that sentence, specifying factor 1/2 before positivity limiting.  Both build passes succeeded, and the final build has no warnings.  Pagewise extracted-text comparison identified page 4 as the only changed page.  Its new rendering passed visual review.  The title, authors, abstract, page count, and two production figures are unchanged.  Submission `f0787a3ef99b` contains this wording revision.

The final provenance record contains 57 checked Git-object identities, including the cited sources, original figures, production data, and executable binary.  Earlier draft records remain preserved, including the identified journal-digest error.

## Final prose review

The third submission was accepted with five prose remarks.  The sixth manuscript addresses all five: the abstract states the counterexample findings, the first heading names verified solver execution, the body identifies Codex and the proving agent, and the repeated proof-engineering sentence is removed.  The end-to-end section, mathematical statements, references, and figures are unchanged.

Both LaTeX passes succeeded, and the 15-page final build has no warnings, undefined references, overfull boxes, or underfull boxes.  Pagewise text comparison found changes only on pages 1 and 9.  Both rendered pages passed visual review.  The extracted abstract matches the revised source and submission metadata.  The PDF downloaded from submission `661f900da98f` has the same SHA-256 as the submitted PDF.

Raw archive policies and reviews, LaTeX logs, and PDF metadata retain their emitted whitespace.  Authored changes pass a separate whitespace check.  Earlier sources, builds, and reviews remain preserved.

marXiv accepted submission `661f900da98f` at 00:05:08 UTC on 16 September 2026 as version 4 of 2609.00006.  The [final review](submission-04/review.txt) states “Accepted” and “No remarks.”  The archive abstract page identifies version 4, 15 pages, two figures, and the submitted title, authors, and revised abstract.
