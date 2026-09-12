# Store preservation outside a memory-write interval

`Memory.WritesRange initial final start stop` records unchanged
non-memory store fields, unchanged primary-memory page count, and
unchanged bytes outside `[start, stop)`.  The store equality preserves
runtime memory caps and identities along with globals, tables, and host
state.  It applies to any host-state type.

Use `write64` after proving that the eight-byte write lies inside the
interval.  Compose consecutive writes with `trans`.  Use `mono` to
enlarge two different intervals before composing them.  These proofs
use the kernel-checked byte-preservation theorem and standard axioms.
`read64` preserves any word whose complete eight-byte range lies outside
the write interval.  The offset-copy invariant uses this consequence for
source reads.  Riemann append composition also uses it to preserve the
target header and the prefix already written by the first copy loop.

The framed raw-array-copy theorems carry this relation through both
loop invariants.  Their combined theorem enlarges the prefix and suffix
intervals to the complete copied payload and composes the relations.
The result provides the store and outside-byte facts needed to preserve
allocator and ownership representations.  The entry remains provisional
pending use in a complete artifact theorem and independent verification.
Riemann initialization's checked append-prefix continuation weakens the
payload interval to its target grid allocation and uses the resulting
`WritesGrid` fact to preserve the represented source grid.
