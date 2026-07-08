# Development Agenda

The verification workspace now carries eleven artifact proofs, a runtime lemma library proved once and consumed everywhere, a tactic layer for the mechanical proof text, and the generic teardown theorem for recursive release.  The per-program cost question that dominated earlier agendas is answered in the small: `fold_sum` went from source to closed input-generic proof in one sitting and 203 lines.  This agenda orders what remains between here and the goal of writing real Lean programs and verifying their shipped WASM routinely.  Items marked as design questions should be settled in discussion before implementation.

## Priority 1: A Real Target Program

Language coverage should now be driven by demand, not speculation.  Pick one program worth shipping — a parser, a state machine, a codec — write it in the accepted subset, and let its gaps set the compiler agenda and its proof set the verification agenda.  The program's teardown consumes the generic release theorems; its computation states the input-generic template; whatever it needs that the subset lacks (strings per [Strings](strings.md), more of the class slice per [Type Classes](typeclasses.md)) becomes the next language increment with a concrete acceptance test.  The deliverable is the program, its proof, and the list of subset gaps it exposed.

## Priority 2: Retire the Per-Shape Teardown Proofs

`release_frees_tree` covers slots-kind ownership trees generically, but `box_free` and `pair_free` still carry their per-shape walk proofs, and the theorem has three restrictions worth lifting in this order: array-kind nodes (so `pair_free`'s branch is covered), shared objects at interior positions, and aliased shared leaves within one release (the `pair_free` pattern where the same child is decremented and then freed).  Re-deriving the two artifacts' release lemmas as corollaries converts several hundred lines of concrete invariant proofs into regression checks of the general theorem and validates each lifted restriction.

## Priority 3: The Fragment-Level Lowering Theorem

The composed `compile_correct` ladder from [Development Plan](plan.md) still begins with `wasm_lower_correct`: for every IR program in a defined fragment, the emitted module, read in the Talos model, computes what `Expr.eval` computes.  The scalar fragment — locals, 64-bit arithmetic, conditionals, lets, calls, loops — covers `gcd` and `order_book`, whose artifact theorems would become corollaries.  The gating design question is unchanged: either prove a lemma connecting the emitter's module representation to the WAT-decoded one, or produce the Talos-model module directly from the compiler's `Wasm` value and validate the byte-level artifact separately.  The second route removes `wasm-tools` from the proof loop and should be evaluated first.

## Priority 4: Remaining Compiler Simplifications

The constructor-field wrapper hoist fixed the measured duplication, but a field that is itself a product whose components carry construction chains still replicates inside the flatten residue; the lets-materializing path handles that shape and the consumers should reach it.  The safety condition on source-level `LeanExe.Runtime.release` (no live alias uses the released value) remains documented rather than checked; a static approximation that rejects releases of visibly aliased values would raise assurance cheaply.  Both items are self-contained and gated by the full suite plus the eleven byte-pinned artifacts.

## Priority 5: Proof-Layer Ergonomics

The mechanical layer shrank with `read_frames` and the arithmetic bridges, but two patterns still cost more than they should: deriving header read-facts in the exact address normal forms the `wp` machinery produces (a normalizing tactic over the `% 2^32` and `% 2^64` layers would remove most remaining `have` blocks), and the invariant-reshaping mismatch where `simp` rewrites a loop invariant between the loop lemma and its re-establishment goal.  Each new proof is the test case; extend `Common.lean` when a pattern appears a third time.
