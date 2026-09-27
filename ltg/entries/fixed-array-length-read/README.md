# Fixed-array length-header load

`FixedArrayLengthRead.program_spec` executes `local.get`, `i32.wrap_i64`,
`i64.load 0`, and `local.set`.  The theorem accepts arbitrary pointer and
destination locals, a memory-read equality, the wrapped address bound,
and an arbitrary continuation.  Its result uses the existing
`FixedArrayFold.resultFrame`, so the checked assignment getters describe
both the loaded word and preservation of every other getter.

The header load uses the same representation for arrays of any element
width.  A represented cell grid supplies the stored length and the
eight-byte bound without a one-word element assumption.  The exact
four-instruction equality remains a consumer obligation.  This entry
has no dedicated compiler annotation.

The Riemann map-input consumer matches the first 12 instructions of the
emitted growth branch and composes two pointer transfers with two header
loads.  The shared load checked in 49 seconds and the consumer in 43
seconds, with standard axioms.  These durations include import and I/O
costs.  The first shared proof retained a wrapped-address addition by
zero.  `UInt32.add_zero` closes that address equality before applying the
memory-read premise.  The entry remains provisional pending complete
initializer and independent artifact verification.

The append setup supplies a second checked consumer.  It composes its
six pointer/parameter transfers, two header loads, and three scalar
count assignments into the exact 32-instruction prefix.  The complete
setup checked in 62 seconds with standard axioms.  Existing
`GridAt.lengthRead` and `GridAt.lengthBound` provide its header premises
directly, so each consumer can reuse the represented-grid API.
