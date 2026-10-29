import LeanExe.Pipeline.AlignedImplements
import LeanExe.ProofKit.AlignedDefs

/-!
The alignment statement of a compiled function.  `ImplementsAligned` adds three facts to
`ImplementsA` on the inputs that `AlignedInput` admits: every run of the entry from some fuel on
makes only aligned 64-bit accesses inside memory, the postcondition's heap is aligned, and the
result's blocks meet `AlignedOutput`.  The last two lie inside the postcondition, so they hold of
the heap that the postcondition chooses, which is the heap a host passes to the next call.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.ProofKit

variable {α β : Type}

/-- `ImplementsA` from an aligned input, with the alignment of every run's accesses, of the final
heap, and of the result's blocks. -/
def ImplementsAligned [Represent α] [Represent β] (aborts : Bool) (m : Module) (entry : Nat)
    (f : α → β) (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Pre x heap store → Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 → AlignedInput heap store params x →
    (∃ N, ∀ fuel ≥ N, AlignedRun fuel m entry store params.reverse env) ∧
    Runs aborts env m entry store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (f x) r) ∧
        Post x heap store heap' final ∧ heap'.Aligned ∧ AlignedOutput final values.reverse (f x)

end LeanExe.Pipeline
