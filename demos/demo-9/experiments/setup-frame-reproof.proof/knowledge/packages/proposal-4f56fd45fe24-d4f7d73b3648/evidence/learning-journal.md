# Learning Journal

## 2026-08-18: Evidence inventory

The accepted run records one 489-instruction function with twenty locals, three loops, memory operations, allocation, and machine arithmetic.  Its archived package contains twenty-four entries across allocation, arrays, compiler motifs, loops, memory, proof construction, and worked examples.  The accepted proof journal reports an array-length dispatch, allocation in both branches, a valid-branch XOR fold, an invalid empty result, and several elaboration boundaries around the fold suffix and continuing loop step.

The run includes the accepted proof, compiler annotations, proof recipes, task features, telemetry, and the proof author's journal.  `PROOF_KIT_SOURCE` contains the supplied ProofKit modules, including the fixed-array fold, fold-body, traversal-input, allocation, result, frame, control, and scalar-transition sources named by the run.  I have not selected a proposal because the exact proof, package bodies, compiler composition, and closest declarations still need comparison.

## 2026-08-18: Proof-journal boundaries

The proof author used the archived length-dispatch, capacity, allocator-window, array-memory, result-store, fold-prefix, fold-structure, fold-body, guarded-back-edge, and compact-suffix support.  The compact-suffix guidance led to two local declarations, after which the remaining loop proof used `continuingProgram_exit_spec`, `singletonResultProgram_spec`, `continuingGuardedProgram_spec`, generated frame accessors, and scalar-transition evaluators.  This path suggests that the existing entries already describe the fold exit and continuing composition, even though the final artifact proof still contains local framing code.

The author encountered one repeated missing boundary before the fold: `constantProgram_spec` produced a `capacityFrame`, but neither the recipe nor the archive supplied a theorem for reading the normalized capacity from its destination local.  The accepted proof reduces that concrete projection once in the valid branch and once in the invalid branch.  A general getter theorem for `capacityFrame` is therefore a candidate, subject to comparison with `FixedArrayCapacity`, frame helpers, the archived capacity entry, and the exact capacity programs in the compiler recipe.

## 2026-08-18: Capacity and allocator comparison

The archived capacity entry names `capacityFrame`, `normalizedCapacity`, and `constantProgram_spec`, while the allocation entry names `region_spec_withTail`; neither archived index names their direct composition.  The current ProofKit source already supplies `capacityFrame_get_capacity`, `capacityFrame_internal_get_capacity`, `normalizedCapacity_toNat_ge_eight`, and `FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail`.  The last theorem composes the exact `constantProgram length stride (offset + 9)` prefix with `region offset stride`, derives the capacity getter and minimum bound, and continues from the same allocation store and frame used by the accepted proof.

For this artifact, offset two, tail four, stride one, and lengths one or zero make `constantCapacityRegion_spec_withTail` match both branch compositions exactly: combined capacity local eleven corresponds to allocator internal local ten, and the twenty-local frame satisfies `2 + 14 + 4`.  A proposed capacity getter or capacity-plus-allocation theorem would duplicate a current checked theorem, so I reject both candidates.  The archive omits the composition theorem from its indexes, but that omission concerns retrieval metadata rather than a missing Lean result.

## 2026-08-18: Fold suffix comparison

The archived fold-structure entry names `singletonResultProgram_spec`, and the accessor entry directs proofs to combine `resultFrame_get_result` with `resultFrame_get_of_ne`.  The accepted `xorSingleton_spec` follows that composition: it starts with accumulator and root getters on the compiler-generated continuing frame, derives both getters on `resultFrame`, and then applies the singleton-result theorem.  The archive records the same pair of getter applications for Demo 9 and Demo 10, so this boundary recurs across addition, multiplication, and XOR folds.

Current ProofKit adds `singletonResultProgram_spec_to`, which generalizes the singleton suffix to an arbitrary target assertion, but it still requires callers to derive the root and result getters on the updated result frame.  A small theorem can take the root getter from the source frame, derive both updated-frame getters with the two existing checked results, and apply `singletonResultProgram_spec_to`.  This candidate differs from the archived guidance by checking the repeated composition once, while leaving compiler-generated frame accessors, output bounds, and the artifact's public postcondition to each proof.

The loop-exit and frame-equality candidates need no new declaration.  `continuingProgram_exit_spec` already keeps the suffix folded, `Frame.ext` now supplies the missing structure equality, and `singletonResultProgram_spec_to` handles the suffix's arbitrary endpoint.  A whole XOR-fold theorem would bind the artifact's generated scalar state and public expected function, so I reject it as artifact-specific repetition of the existing fold-body, fold-prefix, guarded-back-edge, and compact-suffix entries.

## 2026-08-18: First proposal check

I added `singletonResultProgram_spec_to_fromFrame` in the required proposal namespace and imported only `Project.ProofKit.FixedArrayFold`.  The declaration applies `resultFrame_get_of_ne` and `resultFrame_get_result` before invoking `singletonResultProgram_spec_to`, with an arbitrary assertion and the exact `singletonResultProgram` as its conclusion.  The prescribed build completed 3,009 jobs in about twenty-four seconds and accepted the module without diagnostics.

The checked statement removes the two post-update getter premises that caused the accepted proof to construct `hRootAfter` and `hResult`.  It retains the source-frame root and accumulator getters, valid and distinct local premises, payload bound, final-local bounds, and target assertion.  These retained premises correspond to compiler-generated frame accessors or artifact memory and specification facts, so the theorem does not absorb artifact-specific state or arithmetic.

## 2026-08-18: Source-frame interface check

I revised the destination and return premises to refer to the source frame, matching the theorem's root and result premises.  The proof transports those bounds through `resultFrame_params` and `resultFrame_locals_length` before applying the existing suffix theorem.  The prescribed build completed all 3,009 jobs in about five seconds and accepted the revised module without diagnostics.

The revised interface lets an annotation's parameter count and local count discharge every local-bound premise against one frame.  Its only update-sensitive reasoning remains inside the checked declaration: result placement writes the result local, preserves the distinct root local, and preserves the shape needed by the final destination and return locals.  This is the repeated boundary documented by the accepted XOR helper and the archived addition and multiplication fold evidence.

## 2026-08-18: Selection

I selected the checked singleton-result composition.  Its closest theorem, `singletonResultProgram_spec_to`, executes the same exact program and supports an arbitrary assertion, but exposes two premises about the frame after result placement; the proposal derives those facts from the source frame.  Its closest guidance, `annotated-fold-frame-accessors` and `fixed-array-fold-structure`, describes the two getter applications but leaves their composition in each artifact proof, while no archived tactic performs it.

The compiler recipe proves that `function_0_array_fold_0_singleton_result_program` is the shared `singletonResultProgram` with accumulator local one, result local ten, root local seven, destination local four, and return local six.  The proposal keeps all five indices general and depends on no XOR equation, generated frame definition, allocator layout, or public specification.  The accepted 676-line proof and forty-minute Stage 5 telemetry show that the run was substantial, but they do not establish a timing improvement for this lemma, so the selection rests on checked cross-proof repetition and a smaller semantic boundary.

I rejected a worked example because the existing fold entries already record the same proof organization for wrapping addition and multiplication, and XOR changes only the compiler-derived scalar evaluator and fold step.  I rejected capacity, allocator, exit-frame, and arbitrary-postcondition candidates because current ProofKit contains exact checked results for each.  The proposal adds one result-placement-to-singleton composition that current ProofKit and the archived package do not provide as a declaration.
