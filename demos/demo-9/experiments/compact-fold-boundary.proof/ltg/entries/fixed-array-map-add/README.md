# Bounded wrapping-add UInt64 map

Use this entry when `PROOF_RECIPES.json` reports `leanexe.array.map-add.v1` over the complete exported function.  The generated region theorem checks that the decoded function equals `FixedArrayMapAdd.wrapperProgram maximumSize addend`.  `wrapperProgram_spec` proves the length guard, capacity arithmetic, both allocations, dynamic result-length store, transformed-prefix loop invariant, payload stores, and public return.

Apply the complete theorem before opening any internal region.  Its expected function uses `UInt64` addition and therefore matches WebAssembly wrapping arithmetic without an auxiliary overflow premise.  A deterministic starter that already rewrites the region and formal expected result should remain unchanged when the prescribed Lean check accepts it.

The theorem is parameterized by the size bound and addend, while the element transformation remains addition by one constant.  Another map operation needs its own checked adapter or a later transformer-generic theorem.  The existing entry remains useful as a proof pattern even when that broader statement has not yet been justified.
