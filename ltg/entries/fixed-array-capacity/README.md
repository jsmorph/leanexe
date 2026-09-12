# Fixed-array capacity

Use `FixedArrayCapacity.constantProgram_spec` when a length-dispatch recipe supplies a valid- or invalid-branch capacity equality.  The matcher requires the complete constant-length sequence that adds the array header, multiplies length by element stride and word size, rounds to eight bytes, enforces an eight-byte minimum, and writes the selected combined local.  The theorem accepts arbitrary constant `UInt64` length and stride values, local-frame dimensions, continuations, stores, and postconditions.

Apply the exact generated equality or refold the current branch prefix to `constantProgram length stride capacityLocal`.  Prove that the operand stack is empty and that the capacity destination is a valid non-parameter local.  The continuation receives `capacityFrame frame capacityLocal (normalizedCapacity length stride)`, which supplies the capacity-local premise for a following allocator theorem.

Use `capacityFrame_get_capacity` when the next theorem expects a combined-local getter.  Use `capacityFrame_internal_get_capacity` when a shifted allocator expects the corresponding internal-list lookup, and use the three frame-shape declarations for parameter, local-length, and operand-stack premises.  These declarations preserve the capacity frame as a named boundary and avoid reducing its list update inside the allocator continuation.

`normalizedCapacity_toNat_ge_eight` derives the allocator's minimum-capacity premise for every length and stride.  `FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail` composes the capacity prefix with the standard shifted allocator when the capacity destination is `offset + 9`.  Apply the composed theorem only when the residual program has that complete prefix followed immediately by `FixedArrayAllocatorWindow.region offset stride`.

When a concrete `UInt64` equality identifies `normalizedCapacity length stride`, apply `congrArg UInt64.toNat` to obtain the natural-number equality used by memory bounds.  Name that equality before rewriting allocator or payload inequalities.  This avoids unfolding the conditional capacity expression in each later store premise.

The constant theorem covers both sides of a bounded-length branch when each result has a constant array length.  Demo 9 instantiates lengths one and zero in the valid and invalid branches, while Demos 2 and 3 contain the same fixed pair-result calculation for length two.

`localProgram_spec` covers the same sequence with a local-valued length.
It takes a combined getter for that length and returns the same capacity
frame.  Riemann initialization matches this theorem at four emitted
sites: map, append, and both extraction branches.  Their capacity locals
are 54, 59, and 60, respectively.  Those execution equalities preserve
the complete store and every other local.

`normalizedCapacity_toNat_of_fits` proves the exact byte count
`8 + length.toNat * stride.toNat * 8` when adding the seven rounding bytes
also fits UInt64.  It accounts for every modular arithmetic operation
and the final division and multiplication by eight.  The shared proof
checked in 14 seconds with propext and Quot.sound.  Riemann's width-seven
consumer covers lengths through 1,048,576 and checked with the four
execution matches in 13 seconds.  A different minimum or alignment
policy requires another exact program theorem.
