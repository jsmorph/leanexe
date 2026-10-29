import LeanExe.Pipeline.Implements
import LeanExe.Pipeline.AlignedHeap

/-!
The alignment statement between the compiler and the translator to C.  `AlignedInput` is the
premise on a call's input: the heap is aligned, every object that the call consumes starts at a
multiple of 8 and has a capacity that is a multiple of 8, and every region that it reads starts at
a multiple of 8.  `ImplementsAligned` states that, from every input that meets the premises of
`ImplementsA` and `AlignedInput`, the run of the entry makes only aligned 64-bit accesses inside
memory at every fuel from some bound on.  The native statement for the translation without the
alignment test takes both.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.ProofKit

variable {α : Type}

/-- The heap is aligned, the objects that the call consumes start at multiples of 8 and have
capacities that are multiples of 8, and the regions that it reads start at multiples of 8. -/
def AlignedInput [Represent α] (heap : Heap) (store : Store Unit) (params : List Value)
    (x : α) : Prop :=
  heap.Aligned ∧
    (∀ p ∈ Represent.moves store params x, p.toNat % 8 = 0 ∧ capacityAt store p % 8 = 0) ∧
    ∀ r ∈ Represent.reads store params x, r.1 % 8 = 0

/-- From every input that meets the premises of `ImplementsA` and `AlignedInput`, every run of
`entry` from some fuel on makes only aligned 64-bit accesses inside memory. -/
def ImplementsAligned [Represent α] (m : Module) (entry : Nat)
    (Pre : α → Heap → Store Unit → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Pre x heap store → Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 → AlignedInput heap store params x →
    ∃ N, ∀ fuel ≥ N, AlignedRun fuel m entry store params.reverse env

end LeanExe.Pipeline
