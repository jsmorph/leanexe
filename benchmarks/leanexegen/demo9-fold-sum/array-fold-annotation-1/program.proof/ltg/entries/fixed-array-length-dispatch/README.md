# Fixed-array length dispatch

Apply the generated length-dispatch recipe only after the public `TerminatesWith` goal has become a body-level `wp` goal.  `Wasm.TerminatesWith.of_wp_entry_for (f := funcNDef) rfl` performs that conversion for a store-specific proof.  The recipe tactic cannot apply directly to the public theorem because its target begins at the annotated instruction region.

Use `program_spec` or `eqProgram_spec` for exact-size dispatch and `leProgram_spec` for an unsigned maximum-size check.  The `_from` tactic forms accept syntax such as `wp_fixed_array_length_le_dispatch_from hInput at 7, 8`, where `hInput : UInt64Array.At store inputPtr input`, to determine the pointer and represented array before generating frame premises.  Normalize the one local-index premise with the generated function definition only when `decide` cannot reduce the open frame expression.

The semantic theorem executes the represented length load, fixed-width comparison, Boolean normalization, and branch selection.  Its remaining obligations begin at the exact valid and invalid branch programs.  Apply a complete whole-function composition instead when another checked annotation already covers those branches.
