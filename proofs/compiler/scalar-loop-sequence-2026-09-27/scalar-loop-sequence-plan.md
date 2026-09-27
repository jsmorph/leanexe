# Consecutive bounded scalar loops

Measure six fixed native probes before edits: repeated accumulator, dependent
bounds, exits and continue, unused first result, three loops, and word-to-Boolean
composition. Preserve the failures. Start with word-result compositions and
finish their source-to-WASM proofs before expanding Boolean combinations.

Keep existing single-loop extraction first. Introduce a recursive sequence plan
whose leaves reuse the proved word-loop plan and whose bind nodes allocate fresh
locals for the continuation. Earlier result slots must survive later loops. A
function writes the final value into its public result slot only after the whole
sequence. Existing single-loop output should remain unchanged.

First prove reusable finite-store frame lemmas: expression, condition and
statement evaluation survive appending an untouched local suffix. Factor the
existing range-plan execution proof into a body theorem, then use the frame
lemma to execute a leaf with future locals already allocated. Prove exact slot
counts, prefix preservation, and the returned local for recursive sequences.

Give the source its own sequence evaluation/support rules, reusing WordRange at
leaves. Recognize ordinary word lets, retained standard Id annotations, standard
Id binds, metadata and wrappers. Check both computations, even if a result is
unused. Prove totality, complete admission, reconstruction and correctness with
captured bindings matching every future local suffix. A continuation extends
that matching relation with the saved result local.

Reuse scalar arithmetic descriptors, Program.seq and the existing byte decoding,
validation and execution theorems. Prove descriptor admission and local bounds
for every sequence plan; add the sequence branch to function extraction and its
public compiler theorem. Register fixed native/IR/V8 fixtures and malformed input
tests, including zero-count ranges. Archive exact evidence, update task.md,
commit and push before Boolean or nested-loop extensions.
