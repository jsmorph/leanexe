# Constant fixed-array capacity

Use `FixedArrayCapacity.constantProgram_spec` when a length-dispatch recipe supplies a valid- or invalid-branch capacity equality.  The matcher requires the complete constant-length sequence that adds the array header, multiplies length by element stride and word size, rounds to eight bytes, enforces an eight-byte minimum, and writes the selected combined local.  The theorem accepts arbitrary constant `UInt64` length and stride values, local-frame dimensions, continuations, stores, and postconditions.

Apply the exact generated equality or refold the current branch prefix to `constantProgram length stride capacityLocal`.  Prove that the operand stack is empty and that the capacity destination is a valid non-parameter local.  The continuation receives `capacityFrame frame capacityLocal (normalizedCapacity length stride)`, which supplies the capacity-local premise for a following allocator theorem.

The theorem covers both sides of a bounded-length branch when each result has a constant array length.  Demo 9 instantiates lengths one and zero in the valid and invalid branches, while Demos 2 and 3 contain the same fixed pair-result calculation for length two.  A capacity derived from a runtime input length, dynamic filtered count, non-eight-byte element width, or a different minimum policy requires another exact program theorem.
