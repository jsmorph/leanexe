import Verified.TreeAllocate
import Verified.ExprSpec

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def treeParentCode {Γ : List Ty} (shape : TreeShape) (r : Fin shape.records)
    (reuse : Option (Var Γ (.treeHeader shape r))) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) : Program :=
  match reuse with
  | none => recordAllocate (shape.width r) base
  | some x =>
    if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      [.localGet (slots.getD x.index default).loc, .localSet base]
    else recordAllocate (shape.width r) base

def treeParentCost {Γ : List Ty} (shape : TreeShape) (r : Fin shape.records)
    (reuse : Option (Var Γ (.treeHeader shape r))) (slots : List Slot) (live : Nat → Bool) :
    Nat :=
  match reuse with
  | none => allocCost (8 * shape.width r)
  | some x =>
    if (slots.getD x.index default).mode = .owned ∧ live x.index = false then 0
    else allocCost (8 * shape.width r)

end Verified
