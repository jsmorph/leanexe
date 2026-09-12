# Compact loop-suffix theorem boundary

Use this method when applying `Wasm.wp_loop_cons` under the complete artifact postcondition reaches the memory limit, times out, or ends without a diagnostic.  First give the loop a compact completion assertion through `Wasm.wp.conseq`.  If proving that consequence inside the public theorem retains the same large context, move the suffix proof into a separate theorem declaration before checking the loop again.

Use `<region>_singleton_result_spec` when the fold recipe provides it.  The generated theorem applies `FixedArrayFold.singletonResultProgram_spec_to`, discharges frame layout and result-placement premises through checked accessors, and accepts the caller's exact final-state postcondition.  The artifact proof supplies the payload bound and its public result fact without rebuilding the accumulator, root, parameter, local-length, or result-local projections.

Use `FixedArrayFold.singletonResultProgram_spec` when the proof benefits from the smaller fixed `singletonResultPost` assertion.  Use `singletonResultProgram_spec_to` directly when no generated adapter exists but the caller can state its postcondition over the exact final store and frame.  For another suffix, state its program, store relation, required frame values, and output representation facts without mentioning the enclosing loop invariant or public entry decomposition.

Demo 10 supplies provisional evidence for this method.  Four related builds ended without a diagnostic while the fold loop carried its complete result suffix, and three of those builds recorded the six-gibibyte child-memory ceiling; moving the result placement, payload store, singleton reconstruction, and final root transfer into `productSuffix_spec` restored ordinary diagnostics and enabled an independently verified proof.  The shared theorem distills that accepted declaration while preserving arbitrary local roles and fold operations; a fresh fixed-artifact run must still test whether it replaces the artifact-local theorem and changes proof construction.

A manual Demo 11 substitution uses the generated arbitrary-postcondition adapter on the unchanged XOR artifact.  The complete artifact result rebuilt after the proof removed `xorSingleton_spec` and its separate consequence theorem, reducing the behavioral source from 676 to 580 lines and from 2,798 to 2,350 whitespace-delimited words.  This result establishes checked applicability and a structural reduction without measuring proof-generation time.

`BlockLoop.program_spec` composes a block containing a loop with zero
operand parameters and results.  Its invariant and completed-state
predicate require an empty operand stack.  A body proved against
`BlockLoop.stepPost` either takes back edge 0 with a smaller natural
measure or exits at depth 1 with the completed-state predicate.  The
theorem composes that iteration proof with an arbitrary suffix
continuation and handles stack trimming and branch-depth reduction.

Riemann's retry and time-advance loops instantiate this theorem with
different ownership invariants and measures.  Their iteration predicates
instantiate the shared postcondition, which avoids separate match
definitions at composition.  A store-independent measure can leave a
beta redex after invariant decomposition.  `dsimp only` before a measure
rewrite discharges that reduction.  Both loop checks pass with standard
axioms.  Full Riemann artifact verification and a controlled fresh proof
measurement remain open.

The Riemann weighted initializer supplies a straight-line example with
22 compiler-recorded calls and 102 internal locals.  Backtracking among
callee theorems reached the default 200,000-heartbeat limit.  Selecting
the exact compiler-recorded call order still reached that limit at the
third component.  A separate suffix theorem then retained two weights,
the completed density, the staged x-momentum, and the frame dimensions.
Both declarations passed under the unchanged heartbeat and two-minute
runtime limits.  The module checked in 12 seconds with standard axioms.
The suffix accepts arbitrary remaining local values and a caller-supplied
postcondition.  This records checked application of the method without
claiming complete Riemann artifact verification.
