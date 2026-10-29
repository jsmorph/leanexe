import LeanExe.Pipeline.Implements
import LeanExe.Pipeline.AlignedHeap

/-!
The alignment predicates between the compiler and the translator to C.  `AlignedInput` is the
premise on a call's input: the heap is aligned, every object that the call consumes has a pointer
and a capacity that are multiples of 8, and every region that it reads starts at a multiple of 8.
`AlignedOutput` is the matching fact about a call's result: every block that the result owns
starts and ends at a multiple of 8, so a host can meet the next call's `AlignedInput` with it.
`ImplementsAligned`, in `LeanExe/Pipeline/ImplementsAligned.lean`, states both of a compiled
function.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.ProofKit

variable {α : Type}

/-- The heap is aligned, the objects that the call consumes have pointers and capacities that are
multiples of 8, and the regions that it reads start at multiples of 8. -/
def AlignedInput [Represent α] (heap : Heap) (store : Store Unit) (params : List Value)
    (x : α) : Prop :=
  heap.Aligned ∧
    (∀ p ∈ Represent.moves store params x, p.toNat % 8 = 0 ∧ capacityAt store p % 8 = 0) ∧
    ∀ r ∈ Represent.reads store params x, r.1 % 8 = 0

/-- The blocks that a result owns start and end at multiples of 8. -/
def AlignedOutput [Represent α] (store : Store Unit) (values : List Value) (y : α) : Prop :=
  ∀ b ∈ Represent.blocks store values y, b.1 % 8 = 0 ∧ b.2 % 8 = 0

end LeanExe.Pipeline
