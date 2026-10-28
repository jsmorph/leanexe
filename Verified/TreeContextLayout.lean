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

/-- The slots of `n` values of type `t`, each of `w` positions. -/
theorem paramSlots_repeatWidth (t : Ty) (mode : Mode) (Γ : List Ty) (modes : List Mode)
    (w : Nat) (hWidth : t.width = w) : ∀ n base,
    paramSlots (List.replicate n t ++ Γ) (List.replicate n mode ++ modes) base =
      (List.range n).map (fun i => Slot.mk (base + w * i) (t.paramMode mode)) ++
        paramSlots Γ modes (base + w * n)
  | 0, base => by simp
  | n + 1, base => by
    simp only [List.replicate_succ, List.cons_append, paramSlots, List.headD_cons,
      List.tail_cons, hWidth, paramSlots_repeatWidth t mode Γ modes w hWidth n,
      List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append,
      Function.comp_def, Nat.mul_zero, Nat.add_zero]
    congr 2
    · congr 1
      funext i
      congr 1
      rw [Nat.mul_succ]
      omega
    · congr 1
      rw [Nat.mul_succ]
      omega

theorem paramModes_fn {n : Nat} (ts : Fin n → Ty) (mode : Mode) (Γ : List Ty)
    (modes : List Mode) {m : Mode} (hb : ∀ i, (ts i).paramMode mode = m) :
    paramModes (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes) =
      List.replicate n m ++ paramModes Γ modes := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tysOfFn, List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, hb 0, ih (fun i => ts i.succ) (fun i => hb i.succ)]

theorem paramSlots_fn {n : Nat} (ts : Fin n → Ty) (mode : Mode) (Γ : List Ty)
    (modes : List Mode) {m : Mode} (hWidth : ∀ i, (ts i).width = 1)
    (hb : ∀ i, (ts i).paramMode mode = m) : ∀ base,
    paramSlots (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes) base =
      (List.range n).map (fun i => Slot.mk (base + i) m) ++
        paramSlots Γ modes (base + n) := by
  induction n with
  | zero => intro base; simp [tysOfFn]
  | succ n ih =>
    intro base
    simp only [tysOfFn, List.replicate_succ, List.cons_append, paramSlots, List.headD_cons,
      List.tail_cons, hWidth 0, hb 0, ih (fun i => ts i.succ) (fun i => hWidth i.succ)
        (fun i => hb i.succ),
      List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append,
      Function.comp_def, Nat.add_zero]
    congr 2
    · congr 1
      funext i
      congr 1
      omega
    · congr 1
      omega

theorem TreeShape.wordTy_width (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.words r)) : (shape.wordTy r i).width = 1 :=
  shape.elem_width r i

theorem TreeShape.wordTy_paramMode (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.words r)) (mode : Mode) : (shape.wordTy r i).paramMode mode = .borrowed :=
  rfl

theorem TreeShape.arrayTy_width (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.arrays r)) : (shape.arrayTy r i).width = 1 :=
  rfl

theorem TreeShape.arrayTy_paramMode (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.arrays r)) (mode : Mode) : (shape.arrayTy r i).paramMode mode = mode :=
  rfl

theorem TreeShape.context_length (shape : TreeShape) (r : Fin shape.records) (Γ : List Ty) :
    (shape.context r Γ).length = shape.bindCount r + Γ.length := by
  simp [TreeShape.context, TreeShape.bindCount, tysOfFn_length, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem TreeShape.slots_append (shape : TreeShape) (r : Fin shape.records) (base : Nat)
    (mode : Mode) (rest : List Slot) :
    shape.slots r base mode rest = shape.slots r base mode [] ++ rest := by
  simp [TreeShape.slots, List.append_assoc]

theorem TreeShape.slots_length (shape : TreeShape) (r : Fin shape.records) (base : Nat)
    (mode : Mode) :
    (shape.slots r base mode []).length = shape.bindCount r := by
  simp [TreeShape.slots, TreeShape.bindCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem TreeShape.paramModes (shape : TreeShape) (r : Fin shape.records) (mode : Mode) :
    paramModes (shape.context r []) (shape.modes r mode []) = shape.modes r mode [] := by
  simp only [TreeShape.context, TreeShape.modes, Verified.paramModes, List.headD_cons,
    List.tail_cons, paramModes_fn _ _ _ _ (fun i => shape.wordTy_paramMode r i _),
    paramModes_fn _ _ _ _ (fun i => shape.arrayTy_paramMode r i _),
    paramModes_repeat, Ty.paramMode]

theorem TreeShape.paramSlots (shape : TreeShape) (r : Fin shape.records) (mode : Mode)
    (base : Nat) :
    paramSlots (shape.context r []) (shape.modes r mode []) base = shape.slots r base mode [] := by
  simp only [TreeShape.context, TreeShape.modes, TreeShape.slots, Verified.paramSlots,
    List.headD_cons, List.tail_cons, Ty.width,
    paramSlots_fn _ .borrowed _ _ (shape.wordTy_width r) (fun i => shape.wordTy_paramMode r i _),
    paramSlots_repeat (.tree shape) mode _ _ rfl,
    paramSlots_fn _ mode _ _ (shape.arrayTy_width r) (fun i => shape.arrayTy_paramMode r i _),
    paramSlots_repeatWidth .bytes mode [] [] 2 rfl, Ty.paramMode, List.append_nil]

theorem TreeShape.slots_modes (shape : TreeShape) (r : Fin shape.records) (mode : Mode)
    (base : Nat) :
    (shape.slots r base mode []).map Slot.mode = shape.modes r mode [] := by
  rw [← shape.paramSlots r, paramSlots_modes, shape.paramModes r]

theorem TreeShape.modes_borrowed (shape : TreeShape) (r : Fin shape.records) :
    shape.modes r .borrowed [] = List.replicate (shape.bindCount r) .borrowed := by
  simp only [TreeShape.modes, TreeShape.bindCount, List.replicate_add,
    List.replicate_one, List.nil_append, List.append_nil, List.cons_append, List.append_assoc]

theorem TreeShape.slots_borrowed (shape : TreeShape) (r : Fin shape.records) (base i : Nat) :
    ((shape.slots r base .borrowed []).getD i default).mode = .borrowed := by
  rw [← Slot.modes_getD, shape.slots_modes r, shape.modes_borrowed r]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

end Verified
