import Verified.TreeContextSep
import Verified.TreeMatchLoad
import Verified.TreeNodeArgs

namespace Verified

open Wasm LeanExe.Pipeline

theorem LocalsHold.i64_ofFn {s : Locals} {base n : Nat} {words : Fin n → UInt64}
    (h : ∀ i, s.get (base + i.val) = some (.i64 (words i))) :
    LocalsHold s base (List.replicate n .i64) (List.ofFn fun i => Value.i64 (words i)) := by
  intro k hk
  have hkn : k < n := by simpa only [List.length_ofFn] using hk
  simpa [slotIndex, hkn] using h ⟨k, hkn⟩

theorem TreeShape.context_types (shape : TreeShape) (r : Fin shape.records) :
    (shape.context r []).flatMap Ty.types =
      .i64 :: (shape.wordTypes r ++ List.replicate (shape.children r) .i64) := by
  have h := treeArgs_types shape r
  simp only [List.append_nil] at h
  simp only [TreeShape.context, List.flatMap_cons, List.append_nil, h]
  rfl

/-- The locals of a record's header, words, and children hold its branch's values. -/
theorem LocalsHold.treeFields {s : Locals} {shape : TreeShape} {r : Fin shape.records} {base : Nat}
    {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {pointers : Fin (shape.children r) → UInt64}
    (hPtr : s.get base = some (.i64 p))
    (hWords : ∀ i, s.get (slotIndex s.positions (base + 1 + i.val) (shape.elem r i).slotType) =
      some (typedValue (shape.elem r i).slotType (shape.slotWords r words i)))
    (hChildren : ∀ i, s.get (base + 1 + shape.words r + i.val) = some (.i64 (pointers i))) :
    LocalsHold s base ((shape.context r []).flatMap Ty.types)
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i)))) := by
  have hHead : LocalsHold s base [.i64] [.i64 p] := by
    intro k hk
    have hk0 : k = 0 := by simp only [List.length_singleton] at hk; omega
    subst k
    simpa [slotIndex] using hPtr
  have hWordHold : LocalsHold s (base + 1) (shape.wordTypes r) (shape.wordValues r words) := by
    intro k hk
    have hkn : k < shape.words r := by
      simpa only [TreeShape.wordValues, List.length_ofFn] using hk
    have hType : (shape.wordTypes r).getD k .i64 = (shape.elem r ⟨k, hkn⟩).slotType := by
      simp [TreeShape.wordTypes, hkn]
    rw [hType]
    simpa [TreeShape.wordValues, hkn] using hWords ⟨k, hkn⟩
  have hTail := (LocalsHold.append (tys1 := shape.wordTypes r)
    (tys2 := List.replicate (shape.children r) .i64)
    (first := shape.wordValues r words)
    (second := List.ofFn fun i => Value.i64 (pointers i))
    (by simp [TreeShape.wordValues, TreeShape.wordTypes])).mpr
      ⟨hWordHold, by
        simpa only [TreeShape.wordValues, List.length_ofFn] using LocalsHold.i64_ofFn hChildren⟩
  have hAll := (LocalsHold.append (tys1 := [.i64])
    (tys2 := shape.wordTypes r ++ List.replicate (shape.children r) .i64)
    (first := [.i64 p]) (by rfl)).mpr ⟨hHead, hTail⟩
  simpa only [shape.context_types r, List.singleton_append] using hAll

theorem treeFields_variable_regions {heap : Heap} {store : Store Unit} {s : Locals}
    {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {base : Nat} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {children : Fin (shape.children r) → Tree shape}
    {pointers : Fin (shape.children r) → UInt64}
    (hPointers : ∀ i, pointers i = store.mem.read64
      (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
    (hRep : Env.Rep (paramMode (shape.context r []) (shape.modes r mode [])) heap store
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape r words children .nil))
    (hold : LocalsHold s base ((shape.context r []).flatMap Ty.types)
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i))))) :
    ∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
      LocalsHold s ((shape.slots r base mode []).getD x.index default).loc t.types ws →
      ws.length = t.width →
      ∀ b ∈ t.regions ((shape.slots r base mode []).getD x.index default).mode store ws
        ((Env.treeFields shape r words children .nil).get x),
        b ∈ (Ty.tree shape).regions mode store [.i64 p] (.node r words children) := by
  intro t x ws hLocal hLength b hr
  have hPointers' : pointers = fun i => store.mem.read64
      (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) :=
    funext hPointers
  subst pointers
  have hSlot := paramSlots_getD x (shape.modes r mode []) base
  rw [shape.paramSlots r] at hSlot
  rw [hSlot] at hLocal hr
  obtain rfl := LocalsHold.unique hLocal (hold.var x) (hLength.trans (hRep.var x).length.symm)
  exact treeFields_regions_subset store shape r mode p words children b (hRep.regions_var x b hr)

end Verified
