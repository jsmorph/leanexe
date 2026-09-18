import Project.ProofKit.PackedReleaseMany
import Project.ProofKit.LocalPrefix

namespace Project.ProofKit.PackedReleaseMany
open Wasm

def Bindings (items : List Item) (frame : Locals) : Prop :=
  ∀ item ∈ items, frame.get item.ownerLocal = some (.i64 item.node.root)

theorem Bindings.cons {items : List Item} {frame : Locals} (h : Bindings items frame)
    (item : Item) (hItem : frame.get item.ownerLocal = some (.i64 item.node.root)) :
    Bindings (item :: items) frame := by
  intro other hOther
  rcases List.mem_cons.mp hOther with rfl | hOther
  · exact hItem
  · exact h other hOther

theorem Bindings.prefix {items : List Item} {before after : Locals} {count : Nat}
    (h : Bindings items before) (hParams : after.params = before.params)
    (hPrefix : after.locals.take count = before.locals.take count)
    (hBefore : count ≤ before.locals.length) (hAfter : count ≤ after.locals.length)
    (hIndices : ∀ item ∈ items, item.ownerLocal < before.params.length + count) :
    Bindings items after := by
  intro item hItem
  exact (Frame.get_of_take_eq hParams hPrefix hBefore hAfter (hIndices item hItem)).trans (h item hItem)

#print axioms Bindings.prefix

end Project.ProofKit.PackedReleaseMany
