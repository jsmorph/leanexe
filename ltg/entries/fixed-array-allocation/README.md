# Fixed-array allocation

Use this entry when the decoded program contains LeanExe's fixed-array allocator and the formal precondition fixes an empty free list with enough existing memory.  `Allocation.bumpFacts` packages heap arithmetic, header addresses, overflow exclusion, and the no-growth decision.  The complete allocator theorems additionally execute free-list search, header stores, global updates, and returned-root assignment.

Match the exact instruction region before applying a semantic theorem.  `FixedArrayAllocator.region_spec` covers the canonical fourteen-local layout, while `FixedArrayAllocatorWindow.region_spec_withTail` covers a uniform combined-local shift and unused trailing locals.  Continue from the theorem's named allocation store and frame instead of reducing allocator instructions again.

Derive one `bumpFacts` value and reuse its projections for every capacity, address, and memory-bound obligation.  `wordAddress` and `wordAddress_toNat` match the generated result-length and payload addresses.  A failed exact-region match should remain in the journal because it may identify another allocator layout worth adding as a separate motif.

Use `FixedArrayPairResult.input_preserved_by_alloc` when the input representation lies below the allocation base.  The theorem preserves the complete input array across the allocator's six header writes and page-preserving store construction.  Applying it avoids reproving byte equality below the allocation base through six separate `Memory.write64_bytes_before` steps.

Read the allocator header fields according to the checked `region` definition.  The element-type field and stride field are distinct, so an element width such as `2` does not determine the theorem's `stride` argument.  After applying a shifted-window theorem, invoke `wp_alloc_window` with its required square-bracket list of focused simplification facts.

Use `wp_alloc_to_store` when broad reduction crosses the next memory operation or structured control boundary.  The opt-in `wp_alloc_to_store_lists` and `wp_alloc_window_lists` variants also normalize concrete list lengths and head or successor lookups without changing the established tactics used by accepted proofs.  Name the post-allocation store and frame before repeated use so each call reduces a bounded expression rather than the allocator's nested updates.
