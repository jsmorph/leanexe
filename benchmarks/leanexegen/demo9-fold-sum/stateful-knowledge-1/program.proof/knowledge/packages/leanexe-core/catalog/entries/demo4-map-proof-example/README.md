# Demo 4 complete map starter

This example records the proof organization used for the bounded wrapping-add map.  The starter rewrites the exact decoded function to `FixedArrayMapAdd.wrapperProgram`, rewrites the formal expected function to the theorem's expected result, and applies `wrapperProgram_spec`.  The initial prescribed Lean check succeeded, so the agent retained the candidate unchanged.

The example supports a general ordering decision: whole-function semantic theorems precede loop, allocator, and store-level methods.  The accepted proof contains only public precondition decomposition, two checked equalities, and the theorem application.  Its proof-generation session still spent time asking the agent to confirm a proof that Lean could accept directly.

The task catalog excludes this entry from a measured proof of the same artifact digest.  The entry can guide unrelated bounded-map artifacts while its one-consumer status remains visible.  Consult `fixed-array-map-add` for the importable checked theorem and its full premise summary.
