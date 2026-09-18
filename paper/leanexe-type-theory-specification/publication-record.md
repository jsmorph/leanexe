# Publication record

## Current accepted result

[marXiv:2609.00005v6](http://127.0.0.1:8405/abs/2609.00005v6), “The LeanExe Subset: Types, Extraction, and Execution,” by Codex GPT-6 and Jamie Stephens, was accepted on 2026-09-18.  Its primary classification is cs.PL, with cs.LO as the secondary classification.  The report uses source checkpoint `df70a0a56dd909ce2a4685faba5498bdcaf01e81`.

The accepted local source is [the v9 manuscript](v9/main.tex), and its PDF is [the final v9 build](v9/pass-01/main.pdf).  The archive PDF equals the submitted file byte for byte.  Its SHA-256 is `20eb9f570d15616e6bb0688b9dd2280c2ec10fbe1ef02610473b89d4486e9873`.  The [verification record](submission-06/verification.json) records the identity and metadata checks.

The archive family had public static export enabled when this revision was submitted.  The replacement inherited that setting.  The [prior archive record](submission-03/prior-archive-page.html) and accepted submission record preserve the checked controls.  This task changed no export setting.  Earlier records that say export was off describe its setting on 2026-09-11.

## Completeness review and proof scope

The [completeness review](v6/revision-notes.md) compares the previous report with the new checkpoint.  It adds binary32 arithmetic and precision conversion, packed word reads and construction, current evaluation and ownership rules, and a theorem form for checking a compilation against its Lean algorithm.  The [source identities](evidence/source-identities-v3.json) fix the implementation, documentation, tests, and proof declarations used in that review.

The report identifies the five binary32 source/Talos equalities, packed-read and construction theorems, reusable generator and allocation-preservation lemmas, and the completed four-byte inference theorem.  The full pretrained GPT-2 artifact theorem remains open at the cited checkpoint.  The report distinguishes deterministic Talos NaN words from the WebAssembly standard's permitted NaN outcomes.  Precision-conversion source-model proofs also remain open.

The two mathematical layout propositions retain their stated domain definitions.  Shape-sensitive acceptance still uses named compiler recognizers.  Independent source semantics, mechanized acceptance judgments, and a general compiler-refinement theorem remain open.  Per-compilation source proofs state the selected module, Lean function, representation relation, and resource premises.

Both original source-audit findings persist at the new checkpoint: the entry-name rejection set omits runtime exports, and the accepted layouts lack a general child-mask width bound.  This report task ran no Lean build, compiler, verifier, or runtime reproducer and added no dependency.  Its implementation findings remain source-audit results.

## Submission and review history

The first report was accepted as [version 1](http://127.0.0.1:8405/abs/2609.00005v1), submission `d75fc8acf1bc`.  The [first review](submission-01/review.txt) asks the report to identify excluded evidence declarations, identify the release judgment, state which argument supplies Nat fuel, and replace an announcing paragraph opener.  The [second-version clarification record](v5/revision-notes.md) and [declaration evidence](evidence/editorial-clarifications-v2.md) address those four remarks.

The archive accepted submission `aca93998161c` as [version 2](http://127.0.0.1:8405/abs/2609.00005v2).  The [second review](submission-02/review.txt) requests periods in place of independent-clause semicolons in Table 2's array-read and map/modify descriptions.  Version 3 makes those edits along with the terminology and completeness revisions.

Submission `b778e0a57bba` was accepted as version 3.  Its [review](submission-03/review.txt) states “Accepted.”  It records one remark:

> Requirement 9: “The proof workspace pins Talos revision” introduces Talos without identifying it.  Define Talos and its role in the WebAssembly proofs at this first mention.

The [v7 manuscript](v7/main.tex) identifies Talos at first mention as a Lean WebAssembly execution model and proof system.  Submission `cfc499017620` was accepted as version 4.  Its [review](submission-04/review.txt) requests two clarifications:

> Requirement 9, Section 5.1: “Report classification and complete extraction therefore have different result objects.”  Define the paper-specific term “report classification” and identify the result objects being compared.

> Requirement 12, Register and Terminology, Section 4.1: “a live allocation root whose lifetime covers the visible range.”  Distinguish allocation bounds from lifetime.  State that the allocation contains the visible byte range and remains live during its use.

The [v8 manuscript](v8/main.tex) addresses both.  Submission `4f0f9900fbc7` was accepted as version 5.  Its [review](submission-05/review.txt) identifies one type-description error:

> Requirement 12, Register, Table 2: “Map body has type υ and returns Array υ.”  The callback body has result type υ, and the map operation has result type Array υ.  The sentence attributes both types to the body.

The [v9 manuscript](v9/main.tex) assigns each result type to the correct expression.  Submission `268f33c99394` was accepted as version 6.  Its [final review](submission-06/review.txt) states “Accept” and “No remarks.”  All six archive submissions were accepted.

## Document and archive checks

The final v9 build has 16 pages.  Its title, authors, abstract, and page count match the extracted PDF text and archive metadata.  The final LaTeX log has no warnings, undefined references, or overfull boxes.  Visual inspection across the revisions covered the title page, per-compilation theorem, proof inventory, allocation representation, compilation graph, and primitive table.  The archive download equals the submitted PDF byte for byte.

The [upload record](submission-03/upload-attempts.md) records the sandboxed connection failure and successful direct curl retry.  The original [font-related build failure](v1/pass-01/main.log) and both earlier submitted sources and PDFs remain unchanged.  Every submitted revision has a retained source, PDF, metadata record, and review.  Unsubmitted TeX passes reuse their build directory.

The [publication file list](publication-files.txt) selects the files recorded in Git.  Raw HTTP headers, build logs, extracted text, review text, policy snapshots, and HTML records retain their original whitespace and line endings.  Duplicate downloaded PDFs, auxiliary files, preview images, and pending-review captures remain local.
