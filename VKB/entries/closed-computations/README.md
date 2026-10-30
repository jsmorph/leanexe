# Closed computations

Many steps of a program proof are closed facts: a table entry, a constant of a standard, the address of a table in the initial store, or the bytes of an emitted file.  `decide +kernel` proves such a fact by having the kernel evaluate it, and the library uses it in 556 files.  The elaborator's plain `decide` often stops at its recursion limit on the same goals.

Do not use `native_decide` or `bv_decide`.  Both add an axiom that trusts compiled code, and the library's theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.  The SHA-512/t initial values of the copied FIPS 180-4 transcription were proved with `native_decide`, and they now use `decide +kernel`, which takes 40 seconds.

When the kernel's evaluation runs deep, raise the limit for one declaration with `set_option maxRecDepth N in`.  `Library.Hashing.Crc.ready_initial` uses 10,000, because the address of the second CRC table depends on the size of the first.  The file theorems use 100,000, because the bytes they compare nest as deep as the file is long.  Lean also refuses to evaluate a power whose literal exponent exceeds `exponentiation.threshold`, 256 by default, so a proof that evaluates such a power sets that option.

A goal that `decide +kernel` takes minutes to check usually states more than it needs.  Check constants as whole words rather than bit by bit, as the SHA-3 proofs check their round constants as lanes.  Prove a table's entries against a short definition once, rather than at every use.
