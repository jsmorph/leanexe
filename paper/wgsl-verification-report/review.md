# WGSL branch review

Reviewed source: `ba9f02ce930243a3d35d4d10df6f9c97850ca1e8`, fetched from `origin/wgsl` on 19 September 2026.  The local `wgsl` worktree pointer was older.  Review and tests used an isolated detached checkout at `/tmp/leanexe-wgsl-review`.  No WGSL implementation files were changed.

## Findings

| Finding | Evidence and consequence |
| --- | --- |
| Conditional runtime guarantee | `PackedBackend.Host` specifies completed execution of the certified shaders, exact output bytes, and preservation of the remaining store.  The source/layout lemmas prove the matrix result equals the parent.  The host hypothesis includes success and strict arithmetic and is separate from the theorem's logical axiom dependencies. |
| Hybrid binary boundary | `packed-check.js` imports module declarations from the external Talos parser/emitter.  The parent's exact-binary certificate concerns the unchanged parent artifact.  The report must not transfer that guarantee to the changed hybrid bytes. |
| Body-compiler semantic boundary | `Statement.Implements` is a successful invocation theorem in an explicit statement model.  It covers errors, loops, and addresses.  Separate geometric proofs cover dispatch coverage and disjoint stores.  A refinement to complete WGSL semantics and an interleaved scheduler proof for this grammar remain open. |
| Fresh certificate timeout | The extracted proof corpus timed out after 90 seconds on its first positive shader, `add`.  A separate lexical certificate timed out after 60 seconds.  The token-parser certificate passed, and source equality, static validity, invocation correctness, and shared theorem audits passed.  Lexical certification is a reproduction bottleneck under the repository's one-core limits.  Neither timeout establishes a semantic counterexample. |
| Runtime evidence availability | The journal records complete session proof checks and 6,432,896 exact native logit comparisons.  The generated proof objects, shaders, and full-model reports are in ignored build directories and were unavailable in the fetched checkout.  This review inspected the generation and test code but did not replay the complete session or checkpoint test. |
| Deployment identity | The build checks artifacts before copying them into a bundle.  Native and browser hosts load files later.  There is no independent runtime enforcement that changed files still denote the checked programs. |
| Browser status | Browser host and worker source exist, but the branch records browser validation as pending.  No browser completion is claimed. |
| Stale descriptions | `docs/wgsl/gpt2-verification.md` and the success message in `packed-module.js` still describe complete composition as pending.  The newer packed guide, composition script, and integration journal record the conditional complete result. |

The review found no counterexample to the inspected mathematical statements.  The central result is meaningful within its explicit semantics: shader execution is connected to the named source definition, packed byte equality connects the shader to parent matrix functions, and controller/session proofs use those replacement interfaces.  The external execution premise is strong and must remain visible.

## Source inspection

The review followed `Compile.lean`, the independent parser, `SourceBounds`, `StatementRun`, `StatementProof`, and `BodyExecution`.  It checked the generated proof statements and the allowed-axiom gate.  `PackedBody` preserves ordered accumulation, bias order, matrix offsets, and vocabulary transposition.  `PackedShader` proves each serialized invocation succeeds before using its result projection.  `PackedBackend` distinguishes checked kernels, module declarations, and external host behavior.  `FunctionRegion.Imports` transports a closed portable region by function-index renaming.  `packed-compose.js` rechecks changed controller segments and requires audits for the three named public results.

The native host inspection covered matrix-view keys, external-write/reset invalidation, synchronous readback, and Wasmtime NaN configuration.  Browser inspection covered the worker's staging and completion protocol.  Host source inspection is not a host verification theorem.

The W3C WGSL draft dated 17 August 2026, Section 15.7, confirms the implementation latitude relevant to the strict arithmetic premise: [floating-point evaluation](https://www.w3.org/TR/2026/CRD-WGSL-20260817/#floating-point-evaluation).

## Report review

The first pass checked every central statement against its definition, theorem generator, or cited execution record.  It distinguished per-invocation correctness, whole-session composition, external host premises, and exact-binary verification.  It qualified all full-model execution measurements as branch records and retained the fresh timeout.

The second pass checked the extracted PDF text, notation, citations, terminology, headings, repeated claims, metadata, and scope.  It added the worker and statement-semantics citations, replaced a contrastive review sentence with the proposition it described, and recorded the split lexer/parser outcomes.  Visual inspection covered all eight pages.  Tables, equations, code, citations, and page boundaries are readable.  The final build has no citation or layout warnings.  Submission metadata was extracted from the PDF.  The 33 linked source paths exist at the reviewed checkpoint, and their hashes are retained.

## Editorial review

marXiv accepted submission `cc9cb3fc0b09` as `2609.00012v1`, with five remarks retained in the [editorial decision](submission-01/review.txt).  The archived PDF equals the submitted snapshot.  The reviewer requested: “Attribute the combined guarantee to each accepted compilation.”  Version 2 makes that change, identifies the FP32-to-FP64 sampling adapter, removes the repeated assurance table and its announcement, and identifies the source-build tool in the Python-environment sentence.  The revision has eight pages and one table.  The changed pages were inspected again, and metadata was extracted from the revised PDF.

marXiv accepted submission `6ccabfc4e503` as version 2 with “No remarks.”  The downloaded archive PDF equals the submitted snapshot.

The user's context request produced version 3.  Its abstract and opening section explain LeanExe's overall goal, the reason for targeting matrix operations with GPU execution, and the implementation and proof outcomes before the technical details.  The introduction cites the branch's purpose and integration plan.  It identifies faster parallel matrix computation as the intended benefit and CPU WebGPU as the source of the recorded execution evidence.  It preserves the host, arithmetic, binary-decoding, and browser boundaries.  Two text passes checked the new context against those source documents and the subsequent claims.  All nine PDF pages were inspected.  The build has no citation or layout warnings, metadata matches extracted PDF text, and the source-path record now covers 35 files.

marXiv accepted version 3, submission `94d108d4e47d`, with three style remarks.  The reviewer requested removal of a repeated abstract summary and a content-announcement sentence, and a heading that names the implementation and theorem.  Version 4 makes those three edits and retains the context requested by the user.  The version 3 archive PDF equals the submitted snapshot.  The changed abstract and opening pages passed text and visual review.  The rebuilt nine-page PDF has no citation or layout warnings.

marXiv accepted version 4, submission `05f7275f6514`, with “No remarks.”  The archive, submission, and current report PDFs are byte-identical, with SHA-256 `570e079e645106a2bdf3c556f397ef7573beaba547a3ba878d143651631c3768`.  The publication record and report guide identify this accepted version.
