# Publication record

## Accepted result

[marXiv:2609.00005v2](http://127.0.0.1:8405/abs/2609.00005v2), “The LeanExe Fragment: Types, Extraction, and Execution,” by Codex GPT-6 and Jamie Stephens, was accepted on 2026-09-11.  The primary classification is cs.PL, with cs.LO as the secondary classification.  Public static export is off in the submission and paper records.

The accepted local source is [the v5 manuscript](v5/main.tex), and its PDF is [the final v5 build](v5/pass-02/main.pdf).  The archive's second-version PDF equals the submitted file byte for byte.  Its SHA-256 is `57a2bcaf253c242d82de53ec01b42c6d490bc41bd8eb5243ebefcc3b0f7fe3ef`.  The [verification record](submission-02/verification.json) records the identity and metadata checks.

## Submission and review evidence

The first sandboxed upload could not connect to the local server.  Its [curl error](submission-01/curl-stderr.txt) is preserved.  The authorized escalated request returned a [303 response](submission-01/retry-response-headers.txt) for submission `d75fc8acf1bc`, which the archive accepted as version 1.  The [accepted status record](submission-01/status-03.html) and [first review](submission-01/review.txt) preserve the decision and four remarks.

The first review states “Accept.”  It asks the report to identify the excluded evidence declarations, identify the release judgment, state which argument supplies Nat fuel, and replace the child-mask paragraph's announcing opener.  The [revision record](v5/revision-notes.md) and [clarification evidence](evidence/editorial-clarifications-v2.md) describe the four changes.

The replacement used `replaces=2609.00005` and returned a [303 response](submission-02/response-headers.txt) for submission `aca93998161c`.  The [accepted replacement status](submission-02/status-02.html) records its publication as version 2.  The [second review](submission-02/review.txt) states “Accepted.”  Its remaining remarks are:

> Requirement 12, Grammar and mechanics, Table 2: “Size returns Nat64; emptiness returns Bool; indexed read returns τ or Option τ; default read also takes a fallback τ.” Replace the three semicolons joining independent clauses with periods.

> Requirement 12, Grammar and mechanics, Table 2: “Map body has type υ and returns Array υ; modify body has type τ.” Replace the semicolon joining independent clauses with a period.

The submission cycle ended at this accepted version.  No submission was rejected or placed on hold.  The first archive version remains available with its source, PDF, and review.

## Source and proof boundaries

The report fixes documentation checkpoint `2f3ec33f6e98ad98ac94df277c91e5319763cf9d`.  The [source identity record](evidence/source-identities.json) identifies the inspected files and an empty comparison with `7c7277d1e1ab8bc4ee5b4a014a8b975abb8b8054` for the stated paths.

The report proves two propositions about its stated runtime domains and slot widths.  Shape-sensitive acceptance still uses named implementation functions.  The numeric and memory account uses production lowering and target execution, with explicit representation premises.  Existing emitter, decoder, validator, and exact-artifact declarations support their named boundaries.  Independent source semantics, mechanized acceptance judgments, and a general compiler-refinement theorem remain open.

The export-name finding compares the documented runtime names with the implemented entry-name exclusion.  The child-mask finding identifies a missing general width bound at the Nat-to-i64 mask boundary.  Both retain source-audit status.  This report task ran no Lean build, Lean compiler, verifier, or runtime reproducer and added no dependency.

## Document checks and preserved failures

The final build contains 13 pages.  PDF title, authors, and abstract agree with the compiled source after whitespace normalization, and the archive repeats that metadata.  The final build log has no warnings.  Visual inspection covered the title page, type-domain table, primitive table, recognition paragraph, and binary64 equation across the reviewed drafts and submitted revisions.  The archive download confirms the final PDF's exact byte identity.

The initial LaTeX failure required scalable fonts for microtype expansion.  The existing Latin Modern package resolved it.  The [failed build log](v1/pass-01/main.log) remains unchanged.  All intermediate source drafts, auxiliary outputs, and previews remain local, with the selected publication files listed in [the exact file inventory](publication-files.txt).

Raw output whitespace is evidence.  HTTP headers retain CRLF, build logs retain emitted indentation and trailing spaces, PDF text retains extraction line breaks, and review text retains the archive's wording.  Policy snapshots and accepted-status HTML also remain byte-exact.  Their whitespace must not be normalized to satisfy a source-formatting check.  The two submitted LaTeX sources and PDFs likewise remain unchanged.
