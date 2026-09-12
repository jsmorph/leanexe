# Fixed-array prefix and shifted-suffix copy

Use `FixedArrayCopy.program_spec` when a checked `leanexe.array.erase-copy.v1` equality identifies the compiler's complete prefix and shifted-suffix loop pair.  The theorem treats the payload as raw eight-byte cells, with `skipCells` selecting how many source cells the second loop omits between the copied intervals.  `prefixProgram_spec` and `suffixProgram_spec` remain available when the surrounding proof needs a boundary between the two loops.

Supply exact getters for the source pointer, target pointer, prefix count, suffix count, and counter, together with an empty operand stack and a valid counter local distinct from the other four locals.  The source and target regions must fit both the 32-bit address range and current memory, and they may occur in either order when their complete regions do not overlap.  The continuation receives unchanged page and target-header facts, preserved source-cell reads, copied prefix reads, shifted suffix reads, and a `counterFrame` whose counter equals the suffix count.

For a one-word in-bounds `Array.eraseIdx!`, `eraseIdxProgram_spec` combines the loop theorem with `UInt64Array.At.eraseIdx!_of_reads`.  It assumes a represented source before the target and an already-written target length.  Allocation, the target header store, search, and result transfer remain separate.  Demo 12 matches the shape at width one, and the CLOB `matchFuel` and `limit` functions match it at width five.  The retained CLOB proofs use their own ownership continuations.

Use `prefixProgram_framed_spec`, `suffixProgram_framed_spec`, or
`program_framed_spec` when the continuation needs allocator or ownership
facts.  Each adds `Memory.WritesRange` for the copied destination
interval, preserving all non-memory store fields, pages, and outside
bytes.  The original APIs project from these stronger theorems.

Review for Riemann initialization found that the earlier same-address
read lemma depended on a native bit-vector axiom.  The copy library now
uses `Memory.read64_write64` from the `MemoryRoundtrip` module.
All seven public copy theorems pass standard-axiom audits.  The framed
prefix, suffix, and combined checks took 5.0, 5.5, and 5.8 seconds.
Riemann's `initial_append_prefix_spec` matches the emitted region
`func88/block@4/loop@0/else@14:[125,128)` and applies the framed prefix
theorem to width-seven cells.  Its continuation receives the copied
cell fields, preserved source grid and target header, and `WritesGrid`
for the target allocation.  The focused check took 1.8 seconds with
standard axioms.  The append suffix and extraction use different offset
expressions and require separate matching support.

The retained Demo 12 annotation attempt stopped before compilation
because its Lean 4.31 and Talos pins differ from this checkout's Lean
4.34-rc2 pins.  Complete Riemann application and independent artifact
verification of the stronger support remain open.
