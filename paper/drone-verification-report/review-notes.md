# Report review

## Scope and sources

The report uses the drone source and proof statements at `820b3958`.  The stand-alone LeanExe section uses main at `8dbb8e8a`, including the compiler theorem, supported grammar, and integration record.  The drone checkout remains selected.

The marXiv standards and style manual were read before drafting.  The report attributes historical runtime results to the committed development record because the original drivers and raw logs were excluded from the drone commits.

## Review agenda

- [x] Check formulas and central claims against the Lean statements.
- [x] Complete the focused proof build and inspect the printed axioms.
- [x] Run the native five-station example and compare five native/WASM runs.
- [x] Review prose and limitations, then repeat the review.
- [x] Build the PDF and inspect text, references, and page layout.
- [x] Submit the PDF and follow the first editorial decision.
- [x] Complete editorial review of the first revision.
- [x] Complete editorial review of the requested bibliography revision.

## Technical review

The source review traced the clearance coefficients to `Motion.clearance_identity`, integer guards to `Edges` and `Dynamics`, exact ticks to `Timing`, accumulation bounds to `Costs`, graph optimality to `Planner` and `Output`, and global derivatives to `Trajectory`, `Acceleration`, and `WholeFlight`.  The public execution result in `Spec` covers the generated module, borrowed terrain preservation, exact output, and a conditional 64 MiB memory bound.  The allocation polynomial evaluates to 37,580,992 at the maximum accepted size.

The report distinguishes the generated drone model from an exact-byte theorem.  It states graph optimality, corridor ramps, abstract distance units, acceleration jumps, and the caller's initial heap and budget.  It attributes historical runtime comparisons to `task.md`.  Its description of main's general compiler theorem follows `SourceCorrectness.lean`, the supported-grammar guide, and the completed integration record, read from main without changing branches.

On 2026-09-26, the standard local runner completed `Project.Drone.Spec` and `Project.Drone.SourceChecks` with status zero.  The separate [principal axiom audit](evidence/axioms.log) passed with only `propext`, `Classical.choice`, and `Quot.sound`.  A fresh compiler build emitted a 14,198-byte module.  The report's five runs match native Lean word for word.  Their outputs, exact derived costs, and plotting samples are retained.  Plot interpolation follows horizontal progress as a function of normalized time.

The initial figure-driver run failed when the sandbox blocked Node from starting Wasmtime with `EPERM`.  The authorized run outside the sandbox completed.  The compiler, planner, and proofs required no changes.

## Prose and PDF review

The first review checked the theorem assumptions, equations, name references, and evidence attribution.  The second reviewed the extracted PDF text, source wording, figure captions, and limitations.  Edits removed introductory filler, separated the main/drone proof subjects, fixed spaces in displayed code, and allowed long theorem names to wrap.  Vector figures show actual returned paths and share axis limits for the four 15-station terrains.  The report includes a separate five-station example.

The PDF has extractable text.  The final build is checked for undefined references, missing glyphs, and overfull boxes.  Page images were inspected for the title, equations, theorem text, figure pages, theorem table, and bibliography.  The submission title and abstract are extracted from the final PDF.

## Editorial review

marXiv accepted submission `d321203a9895` as [2609.00019v1](http://127.0.0.1:8405/abs/2609.00019v1) on 2026-09-26.  The [complete review](submission-01/review.txt) is retained verbatim.  The archived version 1 PDF equals the submitted snapshot.

The revision addresses all ten remarks.  It defines source application and decoded-module translation, identifies the module and indexed memory-capacity function, replaces independent-clause semicolons, removes filler and repeated scope statements, describes the elaboration changes, attributes axiom dependencies to the theorems, shortens the GPT-2 overview, removes unused binary-size repetitions, and gives the four longer routes' common time once.  The proof claims and run evidence are unchanged.  Source definitions for the added notation were checked before rebuilding.  The revised 16-page PDF has no layout or citation warnings, and its extracted metadata matches the submission fields.  The revised compiler-theorem page was visually inspected.

marXiv accepted submission `22ebc45b02c0` as version 2.  Its [complete review](submission-02/review.txt) records five style remarks.  The next revision states the binary-identification obligation in the abstract, fixes endpoint agreement, describes terrain preservation without metaphor, and identifies the source of the compiler account.  The bibliography revision already removed the sentence announcing a citation.

The report's local links pass.  The repository-wide documentation check reports a preexisting absolute temporary path in `paper/wgsl-verification-report/review.md`.  That unrelated file remains unchanged.

## Bibliography revision

The user requested one LeanExe background reference, drawn from morphism.com/marxiv.  The bibliography now cites *The LeanExe Subset: Types, Extraction, and Execution*, version 6, whose public page and PDF were checked.  The seven repository entries attributed to Jamie Stephens have been removed.  Source paths and theorem names remain in the body and appendix, and companion evidence retains the inspected revisions.  The compiler-correctness results described here postdate that background report.  The three external references cover Lean, planning algorithms, and the WebAssembly specification.

The final citation revision retains one LeanExe background entry and three external references.  All citation keys resolve, the abstract matches the compiled PDF, and the 16-page build has no layout or citation warnings.  The bibliography page was visually inspected.  The version 2 archive PDF equals its submitted snapshot.  marXiv accepted submission `1f5f9e3f8eb1` as [2609.00019v3](http://127.0.0.1:8405/abs/2609.00019v3).  The archive PDF equals the submitted and local PDFs.  The final title and bibliography pages were visually inspected.

The [final editorial review](submission-03/review.txt) accepts the report with three remarks: it requests citations identifying the Talos source and the separate core type-safety results, and a more specific description of the final nested-branch proof.  The accepted version retains the user's single LeanExe background reference.  The review text is preserved verbatim.
