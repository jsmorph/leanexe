import Verified.AlignedArrayCopy
import Verified.TreeRelease

/-!
The interface of the second stage for `release`.  The verified compiler's proof calls `release`
in three ways: on the null pointer, on a leaf object (an array or a byte buffer), as
`release_leaf_run` states, and on the root of a value of a recursive type, as
`release_tree_run_top` states.  `ReleaseAligned` states the aligned form of each: from an aligned
heap and an object whose blocks start and end at multiples of 8, the run's 64-bit accesses inside
memory are aligned, and the heap after it is aligned.  The flagged `read_release`, `ReadReleaseX`,
follows from it in the third stage.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- What the aligned specifications of `release` would supply. -/
structure ReleaseAligned (m : Module) : Prop where
  /-- A call on the null pointer. -/
  null : ∀ (env : HostEnv Unit) (store : Store Unit) (vs : List Value),
    ∃ N, ∀ fuel ≥ N, AlignedRun fuel m 1 store (.i64 0 :: vs) env
  /-- A call on a leaf object, whose child mask is zero: the run is aligned, and so is the heap
  that `Heap.release` gives. -/
  leaf : ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (ptr : UInt64)
    (vs : List Value), heap.At store → heap.Aligned → heap.Object store ptr →
    store.mem.read64 (ptr - 48).toUInt32 = objectMagic →
    store.mem.read64 (ptr - 40).toUInt32 = 1 → store.mem.read64 (ptr - 8).toUInt32 = 0 →
    ptr.toNat % 8 = 0 → capacityAt store ptr % 8 = 0 →
    (∃ N, ∀ fuel ≥ N, AlignedRun fuel m 1 store (.i64 ptr :: vs) env) ∧
      (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).Aligned
  /-- A call on the root of a value of a recursive type: `release_tree_run_top` with an aligned
  run and an aligned heap after it. -/
  tree : ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (p : UInt64) (n : Node)
    (vs : List Value), heap.At store → heap.Aligned → NodeOwned heap store p n →
    (n.blocks store p).Pairwise regionsDisjoint →
    (∀ b ∈ n.blocks store p, b.1 % 8 = 0 ∧ b.2 % 8 = 0) →
    RunsA false env m 1 store (.i64 p :: vs) fun final out => out = vs ∧
      ∃ heap' : Heap, heap'.At final ∧ heap'.top = heap.top ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → (∀ b ∈ n.blocks store p, regionsDisjoint r b) →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r) ∧
        heap'.Aligned

end Verified
