# Artifact-proof composition plan

Date: 2026-08-11

## Objective and evidence

The next increment will reduce the proof work between a checked loop transition and the public artifact theorem.  The accepted addition, multiplication, and XOR fold proofs already use shared dispatch, capacity, allocation, traversal, scalar-transition, and result-store theorems.  Their remaining journals concentrate on equality between equivalent `Wasm.Locals` records and composition of a completed fold with the singleton result, enclosing branch, and public postcondition.

The work will preserve the artifact-only theorem boundary.  Compiler output may select declarations and generate candidate proofs, but each retained declaration must check against the exact decoded WASM program.  The final theorem will continue to exclude source, compiler IR, emitter declarations, and compiler-correctness assumptions from its import closure.

| Evidence | Observation | Planned response |
|---|---|---|
| Demo 9 addition | Generated accessors removed ten proof-local projection declarations in a manual substitution, but a fresh proof took 2,230.869 seconds and 616 lines. | Preserve the accessor family and address the later composition goals before another timing screen. |
| Demo 10 multiplication | The proof used generated getters but reconstructed other frame facts and composed the singleton suffix locally.  The fresh proof took 2,099.237 seconds and 600 lines. | Test a generic frame-equality interface and a generated suffix adapter without adding multiplication-specific mathematics. |
| Demo 11 XOR | The agent attempted a record literal, tried the unavailable `ext` tactic, and eventually closed one exit-frame equality with `convert` and `rfl`.  It also introduced `xorSingleton_spec` and a separate postcondition consequence theorem. | Add a checked `Wasm.Locals` equality interface first, then add one compact suffix theorem in a separate experiment. |
| LTG metrics | The catalog indexes 61 unique declarations but has no structured tactic-name field, although the proof kit contains 27 distinct tactic commands. | Add tactic metadata after the semantic interfaces stabilize, then validate every advertised tactic name. |

## Controls and measurements

Every comparison will retain the formal specification, generated source, WASM bytes, decoded Talos program, toolchain, model configuration, reasoning setting, machine lane, resource profile, and cache policy.  A manual substitution may establish theorem applicability and proof-structure change, but it provides no proof-generation-time result.  A fresh proof screen will report total Stage 5 time, coding-agent time, outer-check time, edited Lean checks, lines, explicit local declarations, shared declarations used, retrieval behavior, and independent verification.

The first measurement set consists of the existing Demo 9, Demo 10, and Demo 11 frame-accessor packages.  Demo 9 provides the same-binary development case, Demo 10 provides a nearby transfer case, and Demo 11 preserves the held-out XOR result that motivated the residual-goal retrieval rule.  A later demo must freeze its request, specification, source, and WASM before it receives the new completion adapter.

No timing threshold determines retention by itself.  A checked theorem may remain provisional when it shortens proof structure, removes repeated derivations, or transfers across artifacts despite slower generation.  Promotion requires recurring accepted use and a credible argument that the statement describes a compiler or WASM motif rather than one program.

## Phase 1: Local-frame equality

`Project.ProofKit.Frame` will receive a structure-extensionality theorem for `Wasm.Locals` and small projection theorems for operand-stack replacement.  The equality theorem will require equality of the parameter list, internal-local list, and operand stack, matching the data that uniquely determine a frame.  The projection theorems will state that replacing `values` preserves `params`, `locals`, and every combined-local getter.

The extensionality theorem will carry the `ext` attribute so ordinary Lean structure reasoning can find it.  LTG will advertise the named theorem and its intended use before a proof unfolds `Wasm.Locals`, while the existing combined-to-internal projection declarations will remain available for list-index goals.  A focused Lean example will prove equality between two differently presented frames using generated field facts rather than reducing their complete local lists.

The first evaluation will edit copies of the accepted Demo 9 and Demo 11 proofs.  The edits will replace exit-frame and values-only-update reductions where the new declarations apply, while leaving the WASM, invariant, and semantic theorems fixed.  This phase passes when both edited proofs verify independently and the resulting source removes at least one artifact-local frame-equality derivation without adding a program-specific theorem to ProofKit.

- [x] Add `Project.ProofKit.Frame.ext` and values-replacement projection theorems.
- [x] Build `Project.ProofKit.Frame` and its generated LTG declaration check.
- [x] Update the local-frame LTG entry, ProofKit documentation, tests, and metrics.
- [x] Apply the declarations in fixed Demo 9 and Demo 11 proof copies.
- [x] Record theorem use, source-structure changes, and remaining frame goals.

## Phase 2: Completed fold to an arbitrary postcondition

`FixedArrayFold.singletonResultProgram_spec` currently stops at `singletonResultPost`.  A more compositional theorem will execute result-local placement, the payload store, and the return-local transfer while accepting an arbitrary postcondition over the exact final store and frame.  This theorem will remain generic over accumulator, result, root, destination, and return local indices.

The array-fold annotation consumer will then generate one adapter for every matched singleton-result suffix.  The adapter will use the exact selected instruction equality, generated continuing-frame accessors, and the generic theorem to discharge frame layout and result-placement premises.  Its caller will supply the mathematical accumulator value, payload bound, represented singleton result, and final public-postcondition proof.

This division leaves application semantics in the artifact proof while removing repeated target-layout work.  The generic ProofKit theorem will contain no generated function or source definition, and the generated adapter will close only after Lean checks it against the exact decoded region.  Opcode, local-index, interval, and result-layout mutations must prevent generation or make the generated module fail.

- [x] Add the arbitrary-postcondition singleton-result theorem and derive the existing compact-post theorem from it where practical.
- [x] Generate `<fold>_singleton_result_spec` from a matched singleton suffix.
- [x] Publish the generated theorem in `PROOF_RECIPES.json` and structured LTG.
- [x] Add positive and mutation tests for the generated declaration.
- [x] Build regenerated Demo 9, Demo 10, and Demo 11 annotation modules without changing their WASM bytes.

## Phase 3: Controlled proof screens

A manual substitution will first replace `xorSingleton_spec`, its postcondition bridge, and the corresponding Demo 9 and Demo 10 scaffolding.  This establishes whether the new theorem presents the right semantic boundary before another coding-agent session spends time discovering it.  The comparison will count removed local declarations, lines of repeated target reasoning, retained application facts, and any new elaboration cost.

One fresh Demo 9 reproof will then expose the frame equality and completion entries through the structured LTG.  The prompt will retain the residual-goal retrieval checkpoint and require the journal to record whether each declaration was found, applied, or rejected.  A failed or slower run remains evidence and will not receive an unchanged repetition unless its journal identifies a correctable general interface defect.

Demo 10 will test transfer after the Demo 9 interface is fixed.  The later frozen demo will use a fold body with a different scalar-control form or accumulator layout, rather than another binary operation with the same state transition.  No result from a different artifact will be described as a controlled timing comparison.

- [x] Verify manual substitutions for all three existing folds.
- [x] Run one fixed-artifact Demo 9 proof screen and review its journal, proof, and telemetry together.
- [x] Correct only general retrieval or theorem-interface defects identified by that review.
- [ ] Test the corrected interface on Demo 10.
- [ ] Freeze and prove a structurally different fold demo before promoting the completion adapter.

## Phase 4: Structured tactic retrieval

The LTG schema will gain an explicit tactic inventory after Phases 1 and 2 settle the declarations that tactics should invoke.  Each tactic record will name its command token, defining module, applicable goal shape, required hypotheses, generated annotation kinds, and fallback declaration.  Catalog validation will reject a missing command, an unallowed module, or a tactic entry whose underlying declarations fail the generated Lean check.

Category indexes will include tactic names and goal-shape aliases so an agent can find a tactic from a residual goal without loading every proof-kit module.  Proof telemetry and journals will distinguish tactic retrieval, tactic invocation, fallback theorem use, and direct reduction.  The metrics report will add indexed tactic definitions, distinct indexed commands, total supplied commands, and tactic discoverability coverage.

- [ ] Define the tactic metadata schema and validation rules.
- [ ] Index the existing stable array, memory, control, and loop tactics.
- [ ] Generate tactic checks and category-index fields.
- [ ] Extend `tools/ltg metrics` with tactic discoverability measures.
- [ ] Test goal-directed tactic retrieval on the fixed fold packages.

## Decisions and stopping conditions

Frame equality and fold completion remain separate experiments because combining them would obscure which interface changed the proof.  A generated adapter that embeds application-specific fold mathematics fails the design even if it shortens one demo.  A theorem that applies only to one generated namespace remains a checked worked example until its statement can be expressed through a recurring annotation schema.

The phase stops if the new interface crosses the artifact-only import boundary, changes a frozen WASM file, weakens independent package verification, or leaves the same detailed frame and suffix obligations under different names.  A theorem with accepted recurring use may remain in LTG with negative timing evidence, while automatic selection requires reliable applicability and acceptable elaboration behavior.  The next larger step after this plan is a checked cut-point graph only if these smaller composition theorems still leave agents reconstructing control-flow joins.
