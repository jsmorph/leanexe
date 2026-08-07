# Manuscript review record

This record describes three review passes over the 7 August 2026 manuscript.  The reviews cover claims that can be checked against the repository snapshot and cited literature.  They do not substitute for external peer review, independent replication, or an artifact-evaluation committee.

## Pass 1: Technical accuracy and claim boundaries

The first pass checked the manuscript against the artifact registry and draft release record, representative exact-artifact theorems, the binary decoder and validator soundness declarations, the `leanexegen` orchestration code, the conformance record, and the four demo histories.  It confirmed twenty registered exact-artifact packages, the 3,853 Talos passes and six configured imported-memory failures, the twenty-five Wasmtime file passes, and the reported proof-generation times.  It also confirmed that package verification starts from copied package sources and bytes without invoking Codex or the LeanExe compiler.

This pass corrected two boundary claims.  The draft release already records source revision `febed96d02f7654a522fc15dc0e6e256f95a782a`, so the remaining release blocker is its cold-checkout receipt; the manuscript snapshot and Demo 4 results postdate that record.  The three coding-agent tasks receive separate materialized contexts, but the host sandbox does not prove filesystem information non-interference, so the manuscript now distinguishes omitted task context from demonstrable source blindness.

The trust review retained the two material qualifications because the repository evidence supports both.  The pinned Talos semantics mishandles imported-memory identity and maximum limits, although every exact-artifact subject lies in the no-import profile.  Lean 4.31.0 accepts the archived kernel-unsoundness reproduction, and the repository's lexical audit neither repairs that defect nor examines the complete dependency closure.

The timing review found incomplete experimental metadata.  The packages identify the Codex CLI version but record the served model and reasoning effort as unrecorded, and the retained benchmark record lacks a complete host-hardware description.  The manuscript therefore presents exact elapsed times as development history, avoids statistical performance claims, and calls for repeated measurements under a complete experimental record.

## Pass 2: Literature, structure, prose, and typesetting

The second pass compared the related-work discussion with primary sources on WebAssembly semantics, WebAssembly program logics, verified compilation, translation validation, proof-carrying code, native-code checking, Lean automation, and language-model proof search.  The bibliography contains thirty-two cited entries, including WasmCert, WasmRef-Isabelle, SpecTec, Wasm Logic, Iris-Wasm, CertiCoq-Wasm, seL4 binary validation, self-certifying WebAssembly, CompCert, CakeML, VeriISLE, VeriWasm, COPRA, Pantograph, and LeanDojo.  A comparison table now states each system's verification boundary without treating target-level proof, compiler preservation, and runtime checking as interchangeable results.

The prose review removed filler, weak boundary language, and claims that exceeded the implementation evidence.  It preserved negative results and experimental qualifications, including the absence of an out-of-sample confirmation for the final Demo 4 theorem and the variance introduced by coding-agent search.  It also added a reproducible build appendix and explicit publication gaps instead of presenting the development snapshot as a completed release.

The typesetting review compiled the complete citation sequence, scanned the LaTeX and BibTeX logs, extracted the PDF text, and inspected the title page and evaluation tables as rendered images.  The final build reports no undefined citations, undefined references, overfull boxes, or BibTeX warnings.  PDF metadata records the title, anonymous author status, subject, and keywords; the resulting document has eighteen pages in US Letter format.

## Pass 3: Independent acceptance review

The acceptance pass checked the manuscript's quantitative claims against the repository's artifact registry, conformance records, toolchain pins, and retained demonstration measurements.  It corrected the reproduction appendix and software citation to identify commit `04f4170a141ef7bd289f81bc739f66d07471900d`, the first repository snapshot containing every reported Demo 4 result.  It also checked the publication files against the working tree so that generated build files remain excluded while the PDF remains versioned.

The acceptance pass rebuilt the document from the edited LaTeX and BibTeX sources and scanned the final logs for unresolved citations, unresolved references, overfull boxes, and bibliography warnings.  It inspected rendered pages containing the title, evaluation results, related-work comparison, and reproduction record.  The pass retained the anonymous author placeholder and documented publication gaps because author metadata, release qualification, repeated measurements, and independent replication require later decisions or evidence.
