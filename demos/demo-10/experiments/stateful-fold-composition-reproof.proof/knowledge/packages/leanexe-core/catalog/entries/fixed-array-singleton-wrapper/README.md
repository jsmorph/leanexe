# Singleton array around a scalar callee

Use this entry when the complete public function accepts a singleton array, loads its element, calls a scalar function that preserves the store, and returns a newly allocated singleton array.  The generated composition identifies the exact wrapper and callee index.  `wrapperProgram_spec` discharges the public length dispatch, checked load, call boundary, capacity calculation, allocator, result stores, and return.

Prove the scalar callee once and supply its theorem to the wrapper.  The remaining obligations connect the generated formal result with the scalar transform for singleton and non-singleton inputs.  Solve those equations after composition instead of reopening the artifact-level wrapper semantics.

This entry composes with any store-preserving scalar theorem having the required operand-stack shape.  Counter transfer and Euclidean loops are current consumers, but their mathematics stays outside the wrapper theorem.  New scalar motifs should reuse the wrapper without adding their application equations to this entry.
