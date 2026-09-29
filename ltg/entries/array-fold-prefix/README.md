# Array-fold prefix invariant

`ArrayFold.foldPrefix input step initial index` is `Array.foldl step initial` over the first `index` elements of `input`.  `foldPrefix_succ` rewrites the prefix at `index + 1` to one application of `step` to the prefix at `index` and the element `input[index]`, and `foldPrefix_size` rewrites the complete prefix to `input.foldl step initial`.  The definitions apply to any element type, accumulator type, and step function.

`Stmt.fold_spec` states its loop invariant with `foldPrefix`: the accumulator local holds the prefix at the index local's value.  A fold that the compiler produced needs only `Stmt.fold_spec` and the `array-fold-loop` entry.  Use `foldPrefix` directly for a traversal that `Stmt.fold` does not cover, such as a loop in hand-written WASM, and keep overflow, ordering, or other facts about the step in separate lemmas.

Give a large traversal proof its own invariant and measure definitions, and move repeated framing or arithmetic arguments into helper lemmas.  An inline existential invariant in one large theorem can use up the heartbeat allowance during simplification.  Separate declarations also give a failing proof a smaller elaboration boundary.
