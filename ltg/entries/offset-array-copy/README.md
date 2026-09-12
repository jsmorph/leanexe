# Array copy with source and destination offsets

`OffsetArrayCopy.program_spec` executes the raw eight-byte copy loop
emitted by `emitCopyLoop`, `emitCopyLoopAt`, and `emitExtractCopyLoop`.
An absent offset local means zero.  A present offset local contains a
word index into the corresponding payload.  Convert element counts and
offsets to word counts using the element width before applying the theorem.

The count bounds and complete-array separation establish each load and
store bound.  The invariant records copied words and `WritesRange` for
the destination interval.  Source reads follow from the unchanged bytes
outside that interval.  The continuation receives the final counter
frame and can derive unchanged headers, earlier copied words, allocator
state, and unrelated arrays with `WritesRange.read64` and `mono`.

`CopyAddress.program_spec` proves the two address-expression shapes and
preserves an arbitrary operand-stack tail.  Its offset-word identity
uses UInt64 conversion algebra.  The wrap operation remains the exact
32-bit WASM operation.  The enclosing loop supplies the address bounds.

Riemann initialization matches the append suffix at
`func88/block@4/loop@0/else@14:[128,131)` with destination offset local 53.
The full append theorem composes the existing prefix and the offset
suffix, reconstructs the concatenated width-seven grid, and preserves
both input grids.  Extraction matches source offset local 54 at
`func88/then@8:[67,70)` and at
`func88/block@4/loop@0/then@14:[67,70)`.  Its theorem reconstructs the
source prefix and preserves the source grid.  The two complete extraction
prefixes also match through instruction 70.

The address theorem checked in 5.3 seconds, the loop in 10 seconds,
append composition in 19 seconds, and extraction in 7.9 seconds.  All
public audits use standard axioms.  Draft corrections addressed explicit
stack replacement, inaccessible counter support, and the frame trimmed
at the loop back edge.  The entry remains provisional pending a complete
artifact consumer and independent package verification.
