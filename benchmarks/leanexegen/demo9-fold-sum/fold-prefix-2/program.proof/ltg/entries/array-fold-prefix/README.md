# Array-fold prefix invariant

Use `ArrayFold.foldPrefix input step initial index` as the mathematical coordinate for an input-traversal loop.  The loop invariant should equate its accumulator local with this prefix value and bound the traversal index by `input.size`.  The definition applies to any element type, accumulator type, and step function.

`foldPrefix_succ` rewrites the continuing branch to one application of `step` at the bounded element `input[index]`.  `foldPrefix_size` rewrites the exit branch to the complete `Array.foldl` expression.  These theorems separate prefix algebra from WebAssembly frame, load, allocation, and branch obligations.

The earlier byte-array fold proof and Demo 9 both used this invariant shape with different element and arithmetic semantics.  Demo 9's wrapping `UInt64` sum needs no range premise because the shared step remains `UInt64.add`.  Keep overflow, ordering, or application-specific facts outside this entry when another fold operation requires them.

Give a substantial traversal its own invariant and measure definitions, and move repeated framing or arithmetic arguments into focused helper lemmas.  Large inline existential invariants can make one public theorem consume its complete heartbeat allowance during simplification.  Separate declarations also give a diagnostic a smaller elaboration boundary without changing the artifact theorem.
