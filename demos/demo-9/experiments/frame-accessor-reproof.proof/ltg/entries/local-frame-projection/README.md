# Combined-to-internal local projection

Use `Frame.internal_getElem?_of_get` when an invariant names a combined WASM operand through `Locals.get` and the next proof step requests `frame.locals[index]?`.  Use `internal_getElem_of_get` when the goal contains an indexed internal-list getter with its bounds proof.  Both declarations account for the parameter prefix and preserve the invariant's value without exposing the definition of `Locals.get` in the application proof.

Supply the recorded parameter-count equality, the internal-index bound, and the invariant getter.  The combined operand must equal `parameterCount + localIndex`, so a one-parameter function maps operand seven to internal index six.  Keep the result as a named fact and include it only in the focused local-update or arithmetic simplification that needs the internal list.

This projection recurs in the loop proofs for Demos 2, 3, 5, and 9 and inside several checked allocator and result theorems.  It applies to every `Wasm.Value` kind and does not depend on arrays, a particular instruction region, or a fixed local count.  A parameter getter, an invalid local, or a fact after a local update requires the corresponding parameter theorem, bounds proof, or updated-frame getter.
