import Verified.ContextAppend

namespace Verified

theorem paramModes_repeat (t : Ty) (mode : Mode) (Γ : List Ty) (modes : List Mode) :
    ∀ n, paramModes (List.replicate n t ++ Γ) (List.replicate n mode ++ modes) =
      List.replicate n (t.paramMode mode) ++ paramModes Γ modes
  | 0 => rfl
  | n + 1 => by simp only [List.replicate_succ, List.cons_append, paramModes,
      List.headD_cons, List.tail_cons, paramModes_repeat t mode Γ modes n]

theorem paramSlots_repeat (t : Ty) (mode : Mode) (Γ : List Ty) (modes : List Mode)
    (hWidth : t.width = 1) : ∀ n base,
    paramSlots (List.replicate n t ++ Γ) (List.replicate n mode ++ modes) base =
      (List.range n).map (fun i => Slot.mk (base + i) (t.paramMode mode)) ++
        paramSlots Γ modes (base + n)
  | 0, base => by simp
  | n + 1, base => by
    simp only [List.replicate_succ, List.cons_append, paramSlots, List.headD_cons,
      List.tail_cons, hWidth, paramSlots_repeat t mode Γ modes hWidth n,
      List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append,
      Function.comp_def, Nat.add_zero]
    congr 2
    · congr 1
      funext i
      congr 1
      omega
    · congr 1
      omega

theorem TreeShape.context_length (shape : TreeShape) (Γ : List Ty) :
    (shape.context Γ).length = shape.bindCount + Γ.length := by
  simp [TreeShape.context, TreeShape.bindCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem TreeShape.slots_append (shape : TreeShape) (base : Nat) (mode : Mode)
    (rest : List Slot) : shape.slots base mode rest = shape.slots base mode [] ++ rest := by
  simp [TreeShape.slots, List.append_assoc]

theorem TreeShape.slots_length (shape : TreeShape) (base : Nat) (mode : Mode) :
    (shape.slots base mode []).length = shape.bindCount := by
  simp [TreeShape.slots, TreeShape.bindCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem TreeShape.paramModes (shape : TreeShape) (mode : Mode) :
    paramModes (shape.context []) (shape.modes mode []) = shape.modes mode [] := by
  simp only [TreeShape.context, TreeShape.modes, Verified.paramModes, List.headD_cons,
    List.tail_cons, paramModes_repeat, Ty.paramMode]

theorem TreeShape.paramSlots (shape : TreeShape) (mode : Mode) (base : Nat) :
    paramSlots (shape.context []) (shape.modes mode []) base = shape.slots base mode [] := by
  simp only [TreeShape.context, TreeShape.modes, Verified.paramSlots, List.headD_cons,
    List.tail_cons, Ty.width, paramSlots_repeat .word .borrowed _ _ rfl,
    paramSlots_repeat (.tree shape) mode [] [] rfl, Ty.paramMode]
  rfl

theorem TreeShape.slots_modes (shape : TreeShape) (mode : Mode) (base : Nat) :
    (shape.slots base mode []).map Slot.mode = shape.modes mode [] := by
  rw [← shape.paramSlots, paramSlots_modes, shape.paramModes]

theorem TreeShape.modes_borrowed (shape : TreeShape) :
    shape.modes .borrowed [] = List.replicate shape.bindCount .borrowed := by
  simp only [TreeShape.modes, TreeShape.bindCount, List.replicate_add,
    List.replicate_one, List.nil_append, List.append_nil, List.cons_append]

theorem TreeShape.slots_borrowed (shape : TreeShape) (base i : Nat) :
    ((shape.slots base .borrowed []).getD i default).mode = .borrowed := by
  rw [← Slot.modes_getD, shape.slots_modes, shape.modes_borrowed]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

end Verified
