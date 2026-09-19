# Third archive revision

The title and current report use “subset.”  Earlier submitted files retain their original wording.

## Completeness review

The review compares accepted archive version 2 against source checkpoint `df70a0a56dd909ce2a4685faba5498bdcaf01e81`.  The [source identities](../evidence/source-identities-v3.json) fix the inspected implementation, documentation, tests, and proof declarations.

| Subject | Finding and revision |
|---|---|
| Runtime types and public ABI | The type constructors, public-domain restrictions, slot widths, and two layout arguments still match the inspected predicates.  The new operations retain integer-word and byte-array types. |
| Floating-point operations | Add binary32 arithmetic, square root, promotion, demotion, instruction boundaries, and the recognized Talos binary64 names. |
| Packed storage | Add direct-lambda generation, byte-offset reads, little-endian layout, trap conditions, and memory premises. |
| Evaluation and ownership | Add one evaluation of mapped multi-slot values, fold materialization, Nat-tail let sharing, explicit-release preservation, cleanup ordering, and internal-result materialization before public projection. |
| Release validation | Add fresh array map/concatenation and the no-owner-field condition that preserves earlier release eligibility. |
| Per-compilation verification | State a theorem relating a selected module to its Lean algorithm, separating source agreement from binary identity. |
| Completed proof components | Identify all five binary32 source/Talos equalities, the generated packed reader, constructor with free-block reuse, generator loop, and allocation-preservation lemmas. |
| Complete-model proof | Identify the completed four-byte inference theorem and leave the pretrained GPT-2 full-artifact theorem open at this checkpoint. |
| Engine semantics | Preserve the distinction between deterministic Talos NaNs and the WebAssembly standard's allowed NaN results.  Precision-conversion source-model proofs remain open. |
| Earlier source-audit findings | Recheck the export-name mismatch and child-mask width obligation.  Both remain source findings without a new compiled reproducer. |
| Earlier editorial remarks | Replace the independent-clause semicolons in the array-read and map/modify descriptions with periods. |

## Checks

The final PDF has 15 pages and extractable text.  Its title, authors, and abstract match the submission metadata.  The final LaTeX log has no warnings, undefined references, or overfull boxes.  Visual inspection covered the title page and the per-compilation theorem and proof inventory.  The report task ran no Lean, compiler, verifier, or numerical test and added no dependency.
