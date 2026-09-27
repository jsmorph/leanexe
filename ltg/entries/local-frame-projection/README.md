# Local-frame equality and projection

Use `Frame.ext` when two `Wasm.Locals` values have equal parameter, internal-local, and operand-stack lists.  Apply the theorem directly when those three equalities already have names, or use `ext <;> simp_all` when the field equalities follow from the local context.  This avoids record-pattern reconstruction and gives the `ext` tactic the theorem absent from the pinned Talos `Wasm.Locals` definition.

Use `Frame.withValues_get` when a block, branch, or control theorem replaces only `frame.values` and a later premise needs `frame.get index`.  The related `withValues_params`, `withValues_locals`, and `withValues_values` declarations expose the other projections without unfolding the frame or getter.  Prefer these theorems to `simp only [Wasm.Locals.get]`, which expands the combined parameter-and-local indexing operation.

Use `Frame.internal_getElem?_of_get` when an invariant names a combined WASM operand through `Locals.get` and the next proof step requests `frame.locals[index]?`.  Use `internal_getElem_of_get` when the goal contains an indexed internal-list getter with its bounds proof.  Both declarations account for the parameter prefix and preserve the invariant's value without exposing the definition of `Locals.get` in the application proof.

Supply the recorded parameter-count equality, the internal-index bound, and the invariant getter.  The combined operand must equal `parameterCount + localIndex`, so a one-parameter function maps operand seven to internal index six.  Keep the result as a named fact and include it only in the focused local-update or arithmetic simplification that needs the internal list.

Restricted `wp_run` simplification retains optional reads, while ordinary
`simp` can convert bounded reads to indexed getters.  Match the projection
to that residual goal.  For repeated local updates that preserve a
different index, apply `List.getElem?_set_ne` with its index inequality.
Riemann's fourteen-result-local frame proof exceeded the default
heartbeat budget when it expanded every update into an if-expression.
The repeated unequal-index theorem applications discharged those reads
within the original budget.  Its complete frame module checked in
6.9 seconds with standard axioms.

`Frame.parameter_getElem_of_get` handles an operand inside the parameter prefix.  It takes the parameter-index bound and combined getter and returns the indexed parameter value.  Riemann's checked multiplication prefix uses it when opcode simplification exposes parameter zero while the invariant supplies `frame.get 0`.

This projection recurs in the loop proofs for Demos 2, 3, 5, and 9 and inside several checked allocator and result theorems.  It applies to every `Wasm.Value` kind and does not depend on arrays, a particular instruction region, or a fixed local count.  A parameter getter, an invalid local, or a fact after a local update requires the corresponding parameter theorem, bounds proof, or updated-frame getter.

The Demo 11 journal records an exit-frame equality that passed through an invalid record literal, an unavailable extensionality theorem, and a later reflexivity proof after conversion.  Its checked fold-completion substitution now uses `Frame.ext`, while the operand-stack projections retain only focused ProofKit evidence.  The entry remains provisional pending another frame-equality consumer and direct artifact-proof use of the operand-stack projections.
