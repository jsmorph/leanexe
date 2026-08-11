# Review record

## Technical evidence

The technical review checked the generated declaration inventory against `tools/leanexegen-annotations.js` and the shared result-frame theorems against `Project.ProofKit.FixedArrayFold`.  It checked accessor retrieval and use against the retained Demo 9, Demo 10, and Demo 11 proof journals and accepted Lean sources.  It checked every reported time and source count against the retained telemetry, timing records, and walkthroughs, including the absence of a same-artifact timing predecessor for the held-out XOR screen.

The review preserved the logical boundary stated in the report.  Compiler annotations and generated accessors propose checked Lean declarations, while the final exact-artifact theorem starts from frozen binary bytes and a validated translation to the pinned Talos model.  The report makes no source-to-WebAssembly preservation claim and records Talos fidelity as an assumption rather than an established equivalence with the normative semantics.

The review also checked the experiment description against the retained task metadata.  All three proof packages identify `codex-cli 0.147.0`, but they do not record the served model or inherited reasoning setting.  The report therefore treats elapsed times as development observations, uses the fixed-artifact Demo 9 and Demo 10 predecessors only for within-artifact deltas, and labels the Demo 11 comparisons as descriptive.

## Prose and claims

The prose review applied the repository guide and the current marXiv standards and style manual.  It removed repeated absolute measurements from the results prose where the table already provides them, removed abbreviated artifact digests that did not identify the complete byte sequence, and stated the timing result as a negative result.  It checked that the abstract states the problem, implemented contribution, accepted evidence, adverse timing result, and next proof boundaries.

The review defined exact-artifact proof, generated accessors, result-frame accessors, structured retrieval, residual-goal retrieval checkpoints, and Stage 5 before relying on those terms.  It checked each section heading for a specific subject or result and scanned the manuscript for filler words, em dashes, rhetorical questions, banned corporate terms, and unsupported performance language.  The bibliography cites primary work on WebAssembly semantics and program logics, verified compilation, translation validation, self-certifying compilation, Lean automation, retrieval, Talos, and the LeanExe implementation.

## Build and rendered output

The final build ran `pdflatex`, `bibtex`, and two further `pdflatex` passes.  The LaTeX and BibTeX logs contain no undefined citation, undefined reference, overfull box, underfull box, or bibliography warning.  PDF metadata records the exact title, anonymous author, subject, and keywords used for submission.

`pdftotext -layout` extracted all five pages, including the abstract, accessor interface, results table, and bibliography.  Visual inspection covered the title page, accessor declaration figure, results table, results discussion, and final bibliography page.  The rendered text fits the page boundaries, the table remains legible, and the figure's generated declaration names remain intact.

## marXiv revisions

marXiv accepted submission `ac710cc54723` as paper `2608.00034` and returned sixteen remarks.  The first revision defined the frame and retrieval terms, moved the Stage 5 definition before the results table, named the retained baseline packages, and made the coding agent or experimental procedure the actor.  It also removed unused byte-size and execution details, replaced figurative descriptions, reported package verification once, stated the relation to prior WebAssembly work directly, and limited the repeated-retrieval claim to the tested procedure.

marXiv accepted replacement `a71611ba3da5` as version 2 and returned seven narrower remarks.  The second revision removed `exact-artifact proof` from the abstract before its definition, described the measured interval as the direct artifact-proof stage, expanded LTG, and replaced four remaining project terms with literal descriptions.  It also assigned the array behavior to each program, named the Talos behavioral-proof obligation, defined catalog promotion and the object of retention, and replaced `worse` with the measured outcome `longer`.

marXiv accepted replacement `1c0123c43288` as version 3 and returned six remarks.  The third revision defined the input root and effective stop by their concrete roles, removed a table reference to Stage 5 before the term's definition, and resolved the ambiguous antecedent in the validator description.  It replaced statements of intent and boundary metaphors with the frame states and proof obligations at issue, and it specified the scope of the checked representations proposed for future compiler output.

marXiv accepted replacement `3c52df2b887c` as version 4 and returned eight remarks.  The fourth revision replaced an undefined frame name, introduced the structured lemma, tactic, and guidance catalog and its maturity states, and used `residual-goal` consistently as a compound modifier.  It removed a repetitive retrieval column from the results table, identified the local equalities proposed for compiler support, replaced an unmeasured frequency claim, and limited the timing conclusion to the observed longer runs.

marXiv accepted replacement `de47eced761d` as version 5 with no remarks.  The final version has automatic classifications in Programming Languages and Logic in Computer Science and retains the relation to the structured-LTG paper `2608.00029`.  The published record is `2608.00034`, and its title, anonymous author, and abstract match the final PDF and PDF metadata.
