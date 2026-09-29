# Local-frame equality and projection

These lemmas are about raw `Wasm.Locals`, which the IR hides behind `State.toLocals` and `State.get`.  They apply to proofs about hand-written WASM code, such as the runtime functions `alloc`, `retain`, and `release`.  A compiled program's proof uses `State.get`, `State.set?`, and their lemmas instead.

Use `Frame.ext` when two `Wasm.Locals` values have equal parameter, internal-local, and operand-stack lists.  Apply it directly when the three equalities have names, or use `ext <;> simp_all` when they follow from the context.  Use `Frame.withValues_get` when a block, branch, or control theorem replaces only `frame.values` and a later premise needs `frame.get index`.  `withValues_params`, `withValues_locals`, and `withValues_values` give the other fields.  Prefer these lemmas to `simp only [Wasm.Locals.get]`, which expands the combined parameter-and-local indexing.

`Frame.internal_getElem?_of_get` turns a `Locals.get` fact about operand `parameterCount + localIndex` into a fact about `frame.locals[localIndex]?`, and `internal_getElem_of_get` gives the indexed form with its bounds proof.  `Frame.parameter_getElem_of_get` does the same for a parameter.  Each takes the parameter count, the index bound, and the `Locals.get` equation.

For repeated local updates that keep a different index, apply `List.getElem?_set_ne` with the index inequality instead of letting `simp` expand every update into an `if`.  An earlier proof with fourteen local updates exceeded the default heartbeat budget until it made this change.  The lemmas hold for every `Wasm.Value` kind and any number of locals.
