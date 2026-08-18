# Stateful knowledge exercise

This exercise starts from the accepted Demo 11 XOR-fold proof and the default twenty-four-entry knowledge forest.  A live `learn propose` task produced one checked, operation-independent singleton-result adapter, and `learn promote` added it to an isolated two-package forest.  A fixed-artifact Demo 9 reproof then received that forest, produced an accepted schema-nine proof package, and recorded every inspected entry as used or rejected.

| Evidence | Result |
|---|---|
| Demo 11 proposal | Checked `fixed-array-singleton-result-from-frame` theorem with an exact Demo 11 artifact exclusion. |
| Demo 9 reproof | Accepted in 1,638.250 seconds with 650 lines, 2,799 words, and 31,897 bytes. |
| Knowledge evaluation | Eleven core entries used; the learned singleton adapter rejected because the generated exact adapter matched the artifact more closely. |
| Follow-up proposal | Benchmark-local worked example preserving the accepted composition order. |

The [accepted proof package](program.proof/) archives the two-package forest, promoted theorem and evidence, exact Demo 9 artifact, proof journal, accepted proof, telemetry, and knowledge evaluation.  `tools/leanexegen verify -s` accepted this package and rebuilt its exact artifact theorem.  The adjacent [WASM module](program.wasm) is the 1,979-byte artifact with SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

The [follow-up candidate](followup-candidate/) records the next learning pass over the accepted schema-nine package.  Its journal rejects a new fold-step theorem because `FixedArrayFoldBody.continuingGuardedProgram_spec` covers that boundary, and it rejects a setup-frame theorem because the expensive equality depends on the generated frame and local layout.  It preserves the proof as a benchmark-local worked example whose useful content is the order of dispatch, allocation, memory framing, fold setup, loop-body composition, exit, and result construction.

The 1,638.250-second Stage 5 time is 21.0 percent below the earlier 2,074.169-second fold-body reproof, while the proof is 10.5 percent longer by lines.  The time reduction belongs to the combined configuration because the proving agent inspected and rejected the learned theorem.  The measurement covers the current core LTG, compiler recipes, annotations, model behavior, and warm machine state.

The journals identify three changes for later work.  The catalog should expose `FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail` through the capacity and allocation indexes.  The annotation generator should emit the equality between `FixedArrayFold.forwardSetupFrame` and the initial generated continuing frame.  The task-feature extractor should report the checked length dispatch already present in the artifact annotations.
