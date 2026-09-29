# Store preservation outside a memory-write interval

`Memory.WritesRange initial final start stop` says that `final` equals `initial` except in the bytes of memory 0 in `[start, stop)`: every other store field, the page count, and every byte outside the interval are unchanged.  The unchanged fields include memory caps, globals, tables, and host state, for any host-state type.  `read64` gives the value of any word whose eight bytes lie outside the interval.

`refl` starts a chain, `WritesRange.write64` adds an eight-byte store inside the interval, `trans` composes two relations with the same interval, and `mono` enlarges an interval before composing.  A loop that stores into one object carries the relation in its invariant.  The result keeps other objects' representations, for example through `UInt64Array.At.writesRange`.
