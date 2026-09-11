# Report and submission notes

## Scope and source identity

The user requested a report about LeanExe's type theory and specification and authorized submission to marXiv on 2026-09-11.  This directory contains the report sources, rendered revisions, extracted PDF text, source evidence, and editorial records.  Every submitted revision remains unchanged.

The report describes documentation checkpoint `2f3ec33f6e98ad98ac94df277c91e5319763cf9d`.  At task start, HEAD was `7c7277d1e1ab8bc4ee5b4a014a8b975abb8b8054`.  Read-only comparison found no differences in the two specification documents or the inspected extraction, IR, and binary-emission implementation between those revisions.  Root continues the Euler work.  This task owns only this new directory and performs no Git mutations.

## Plan

- [x] Read repository requirements, paper documentation, and the submit-marxiv skill.
- [x] Read the live marXiv standards and style manual before drafting.
- [x] Confirm installed PDF tools and required LaTeX packages.
- [x] Draft the technical report and review claims against source.
- [x] Build and inspect the PDF, including extractable title and abstract.
- [x] Submit with public static export disabled and preserve the response.
- [x] Follow editorial review and record the accepted identifier or stopping condition.

## Work record

2026-09-11: The archive at `http://127.0.0.1:8405` responded to the standards, style, and submission-form requests.  The live standards identify requirements 1 through 5 as rejection grounds and requirements 6 through 12 as remarks.  The installed `pdflatex`, `pdftotext`, `pdfinfo`, and `pdftoppm` tools are available.  No dependency installation, Lean process, compiler, verifier, or numerical process ran for this task.

2026-09-11: Root reviewed the report's two layout arguments and its implementation/refinement boundaries.  The initial PDF build failed because microtype font expansion required scalable fonts.  Existing Latin Modern fonts resolved that failure.  Drafts v1 through v4 and each build pass remain preserved.  Root's binary64 correction now uses an explicit set comprehension and defines the permitted-result set.  The final v4 build has 13 pages and no LaTeX warnings.  PDF title, authors, and abstract match the submission metadata after whitespace normalization.  The final title page, primitive table, and binary64 equation were visually inspected.

2026-09-11: Submission `d75fc8acf1bc` entered review at `http://127.0.0.1:8405/status/d75fc8acf1bc`.  The sandboxed connection failure and successful escalated response are both preserved in the submission record.  The status page confirms that public static export is unchecked.  The submitted PDF is `v4/pass-01/main.pdf`, SHA-256 `fb02518985ea0ad46ec3ed501f2b869bf188cbd3af117df567ccd076e62d11ef`.  No Lean or compiler execution accompanied this submission.

2026-09-11: marXiv accepted the initial submission as `2609.00005`.  The review recorded three requests to identify terms and one paragraph-opening remark.  The replacement source v5 addresses all four.  Submission `aca93998161c` uses `replaces=2609.00005`, preserving the accepted first version.  The replacement PDF again has 13 pages, exact extracted metadata, and no LaTeX warnings.  Its SHA-256 is `57a2bcaf253c242d82de53ec01b42c6d490bc41bd8eb5243ebefcc3b0f7fe3ef`.

2026-09-11: The replacement was accepted as `2609.00005v2`.  Its reviewer recorded two remaining semicolon-to-period grammar remarks in Table 2.  The submission cycle ended at the accepted replacement.  The archived PDF equals the local submitted PDF byte for byte, archive metadata matches the PDF, and the public-export setting remains unchecked.  The README and publication record distinguish selected publication evidence from preserved local intermediate files.
