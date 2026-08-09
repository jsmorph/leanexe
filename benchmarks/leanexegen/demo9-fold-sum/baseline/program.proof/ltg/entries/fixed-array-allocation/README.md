# Fixed-array allocation

Use this entry when the decoded program contains LeanExe's fixed-array allocator and the formal precondition fixes an empty free list with enough existing memory.  `Allocation.bumpFacts` packages heap arithmetic, header addresses, overflow exclusion, and the no-growth decision.  The complete allocator theorems additionally execute free-list search, header stores, global updates, and returned-root assignment.

Match the exact instruction region before applying a semantic theorem.  `FixedArrayAllocator.region_spec` covers the canonical fourteen-local layout, while `FixedArrayAllocatorWindow.region_spec_withTail` covers a uniform combined-local shift and unused trailing locals.  Continue from the theorem's named allocation store and frame instead of reducing allocator instructions again.

Derive one `bumpFacts` value and reuse its projections for every capacity, address, and memory-bound obligation.  `wordAddress` and `wordAddress_toNat` match the generated result-length and payload addresses.  A failed exact-region match should remain in the journal because it may identify another allocator layout worth adding as a separate motif.
