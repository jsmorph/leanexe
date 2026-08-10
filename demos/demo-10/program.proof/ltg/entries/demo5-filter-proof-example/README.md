# Demo 5 complete filter starter

This example records the accepted proof organization for the bounded stable filter.  The starter establishes the exact wrapper equality, aligns both the expected result and branch-sensitive heap reserve, and applies `FixedArrayFilterLt.wrapperProgram_spec`.  Lean accepted the first check without a candidate edit.

The example shows why dynamic result length does not require artifact-local loop reasoning once the checked theorem exposes the right boundary.  The proof retains the input-size bound, allocator globals, page bound, and heap-reserve premise while delegating predicate branches and conditional stores to the library theorem.  This organization reduced the earlier 969-line proof to 70 lines.

The task catalog excludes this entry from a measured proof of the same artifact digest.  Its description may still inform a different filter artifact when the journal records that consultation.  Consult `fixed-array-filter-lt` for the checked declaration, exact annotation kind, and applicability limits.
