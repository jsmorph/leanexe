import Verified.TreeMatchFrame
import Verified.Potential

namespace Verified

open Wasm LeanExe.Pipeline

theorem Env.pot_repeatZero {Γ : List Ty} (store : Store Unit) (s : Locals) (tail : Env Γ)
    (t : Ty) (hZero : ∀ ws value, t.pot store ws value = 0) :
    ∀ n (values : Fin n → t.denote) (first rest : List Slot) (sel : Nat → Bool),
      first.length = n →
      (Env.prependRepeat t n values tail).pot store s (first ++ rest) sel =
        tail.pot store s rest (fun i => sel (i + n))
  | 0, _, first, rest, sel, hLength => by
    have : first = [] := by simpa using hLength
    subst first
    rfl
  | n + 1, values, first, rest, sel, hLength => by
    cases first with
    | nil => simp at hLength
    | cons sl first =>
      simp only [Env.prependRepeat, List.cons_append, Env.pot, hZero, ite_self,
        Nat.zero_add, List.tail_cons]
      rw [Env.pot_repeatZero store s tail t hZero n (fun i => values i.succ) first rest
        (fun i => sel (i + 1)) (by simpa using hLength)]
      congr 1

theorem Env.pot_fnZero {Γ : List Ty} (store : Store Unit) (s : Locals) (tail : Env Γ) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (first rest : List Slot)
      (sel : Nat → Bool), (∀ i ws value, (ts i).pot store ws value = 0) →
      first.length = n →
      (Env.prependFn n ts values tail).pot store s (first ++ rest) sel =
        tail.pot store s rest (fun i => sel (i + n))
  | 0, _, _, first, rest, sel, _, hLength => by
    have : first = [] := by simpa using hLength
    subst first
    rfl
  | n + 1, ts, values, first, rest, sel, hZero, hLength => by
    cases first with
    | nil => simp at hLength
    | cons sl first =>
      have ih := Env.pot_fnZero store s tail n (fun i => ts i.succ) (fun i => values i.succ) first
        rest (fun i => sel (i + 1)) (fun i => hZero i.succ) (by simpa using hLength)
      change (if sel 0 then (ts 0).pot store (s.read (sl.loc) (ts 0).types) (values 0) else 0) +
          (Env.prependFn n (fun i => ts i.succ) (fun i => values i.succ) tail).pot store s
            (first ++ rest) (fun i => sel (i + 1)) = _
      rw [hZero, ite_self, Nat.zero_add, ih]
      congr 1

theorem Env.pot_fnOff {Γ : List Ty} (store : Store Unit) (s : Locals) (tail : Env Γ) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (first rest : List Slot)
      (sel : Nat → Bool), (∀ i, i < n → sel i = false) →
      first.length = n →
      (Env.prependFn n ts values tail).pot store s (first ++ rest) sel =
        tail.pot store s rest (fun i => sel (i + n))
  | 0, _, _, first, rest, sel, _, hLength => by
    have : first = [] := by simpa using hLength
    subst first
    rfl
  | n + 1, ts, values, first, rest, sel, hOff, hLength => by
    cases first with
    | nil => simp at hLength
    | cons sl first =>
      have ih := Env.pot_fnOff store s tail n (fun i => ts i.succ) (fun i => values i.succ) first
        rest (fun i => sel (i + 1)) (fun i hi => hOff (i + 1) (by omega))
        (by simpa using hLength)
      change (if sel 0 then (ts 0).pot store (s.read (sl.loc) (ts 0).types) (values 0) else 0) +
          (Env.prependFn n (fun i => ts i.succ) (fun i => values i.succ) tail).pot store s
            (first ++ rest) (fun i => sel (i + 1)) = _
      rw [hOff 0 (by omega), if_neg Bool.false_ne_true, Nat.zero_add, ih]
      congr 1

theorem Env.pot_treeFields {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ)
    (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape) (base : Nat) (mode : Mode)
    (slots : List Slot) (sel : Nat → Bool)
    (hSel : ∀ i, i < shape.bindCount r → sel i = false) :
    (Env.treeFields shape r words arrays buffers children env).pot store s
        (shape.slots r base mode slots) sel =
      env.pot store s slots (fun i => sel (i + shape.bindCount r)) := by
  change (if sel 0 then 0 else 0) +
    (Env.prependFn (shape.words r) (shape.wordTy r) words
      (Env.prependRepeat (.tree shape) (shape.children r) children
        (Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
          (Env.prependRepeat .bytes (shape.buffers r) buffers env)))).pot store s
      (((List.range (shape.words r)).map (fun i => Slot.mk (base + 1 + i) .borrowed)) ++
        (((List.range (shape.children r)).map
          (fun i => Slot.mk (base + 1 + shape.words r + i) mode)) ++
          (((List.range (shape.arrays r)).map
            (fun i => Slot.mk (base + 1 + shape.words r + shape.children r + i) mode)) ++
            (((List.range (shape.buffers r)).map (fun i =>
              Slot.mk (base + 1 + shape.words r + shape.children r + shape.arrays r + 2 * i)
                mode)) ++
              slots)))) (fun i => sel (i + 1)) = _
  simp only [ite_self, Nat.zero_add]
  rw [Env.pot_fnZero store s _ (shape.words r) (shape.wordTy r) words
    ((List.range (shape.words r)).map (fun i => Slot.mk (base + 1 + i) .borrowed)) _
    (fun i => sel (i + 1)) (fun _ _ _ => rfl) (by simp)]
  rw [Env.pot_repeatZero store s _ (.tree shape) (fun _ _ => rfl) (shape.children r) children
    ((List.range (shape.children r)).map (fun i => Slot.mk (base + 1 + shape.words r + i) mode))
    _ (fun i => sel (i + shape.words r + 1)) (by simp)]
  rw [Env.pot_fnOff store s _ (shape.arrays r) (shape.arrayTy r) arrays
    ((List.range (shape.arrays r)).map
      (fun i => Slot.mk (base + 1 + shape.words r + shape.children r + i) mode)) _
    (fun i => sel (i + shape.children r + shape.words r + 1))
    (fun i hi => hSel _ (by simp only [TreeShape.bindCount]; omega)) (by simp)]
  rw [Env.pot_repeatZero store s env .bytes (fun _ _ => rfl) (shape.buffers r) buffers
    ((List.range (shape.buffers r)).map (fun i =>
      Slot.mk (base + 1 + shape.words r + shape.children r + shape.arrays r + 2 * i) mode))
    slots (fun i => sel (i + shape.arrays r + shape.children r + shape.words r + 1)) (by simp)]
  congr 1
  funext i
  congr 1
  simp only [TreeShape.bindCount]
  omega

theorem TreeShape.slots_getD_suffix (shape : TreeShape)
    (r : Fin shape.records) (base : Nat) (mode : Mode)
    (slots : List Slot) (i : Nat) :
    (shape.slots r base mode slots).getD (i + shape.bindCount r) default =
      slots.getD i default := by
  rw [shape.slots_append r]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [shape.slots_length r]; omega), shape.slots_length r,
    Nat.add_sub_cancel_right]

theorem dyingPot_treeFields {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ)
    (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape) (base : Nat) (mode : Mode)
    (slots : List Slot) (paid : List Bool) (L0 L1 : Nat → Bool) :
    dyingPot store s (Env.treeFields shape r words arrays buffers children env)
      (shape.slots r base mode slots)
      (List.replicate (shape.bindCount r) false ++ paid) L0 L1 =
      dyingPot store s env slots paid (fun i => L0 (i + shape.bindCount r))
        (fun i => L1 (i + shape.bindCount r)) := by
  unfold dyingPot
  have hSel : ∀ i, i < shape.bindCount r →
      (L0 i && !L1 i && paidAt (List.replicate (shape.bindCount r) false ++ paid) i &&
        ((shape.slots r base mode slots).getD i default).mode == .owned) = false := by
    intro i hi
    simp [paidAt, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]
  rw [Env.pot_treeFields _ _ _ _ _ _ _ _ _ _ _ _ _ hSel]
  apply Env.pot_ext
  intro i _
  rw [shape.slots_getD_suffix r]
  simp only [paidAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.length_replicate,
    Nat.add_sub_cancel_right]

theorem dyingPot_treeEntry {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ)
    (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape) (base : Nat) (mode : Mode)
    (slots : List Slot) (paid : List Bool) (L1 live : Nat → Bool) :
    dyingPot store s (Env.treeFields shape r words arrays buffers children env)
      (shape.slots r base mode slots)
      (List.replicate (shape.bindCount r) false ++ paid)
      (fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i)
      (shift (shape.bindCount r) live) = dyingPot store s env slots paid L1 live := by
  rw [dyingPot_treeFields]
  apply dyingPot_congr <;> intro i <;>
    simp [shift, show ¬i + shape.bindCount r < shape.bindCount r by omega]

theorem treeCase_bodyWithin {Γ : List Ty} {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {L0 L1 live : Nat → Bool} {base fieldBase : Nat} {shape : TreeShape}
    {r : Fin shape.records} {mode : Mode}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {heap0 heap : Heap} {store0 store : Store Unit} {s0 s : Locals}
    {fresh : List (Nat × Nat)} {m : Module} {rootCost bodyCost : Nat}
    (h0 : Holds env slots L0 base heap0 store0 s0)
    (hStep : Step heap0 store0 (Holds.KeepDying env slots L0 L1 store0 s0) heap store fresh)
    (hFrame : Frame base s0 s) (hL1 : ∀ i, L1 i = true → L0 i = true)
    (hLive : ∀ i, live i = true → L1 i = true)
    (hTop : heap.top.toNat ≤ heap0.top.toNat + dyingPot store0 s0 env slots paid L0 L1 + rootCost)
    (hWithin : heap0.Within store0 m
      (dyingPot store0 s0 env slots paid L0 live + rootCost + bodyCost)) :
    heap.Within store m
      (dyingPot store s (Env.treeFields shape r words arrays buffers children env)
        (shape.slots r fieldBase mode slots) (List.replicate (shape.bindCount r) false ++ paid)
        (fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i)
        (shift (shape.bindCount r) live) + bodyCost) := by
  rw [dyingPot_treeEntry, dyingPot_step h0 hStep hFrame hL1 L1 live (fun _ hi => hi)]
  have hSplit := dyingPot_split (store := store0) (s := s0) (env := env) (slots := slots)
    (paid := paid) L0 L1 live hL1 hLive
  unfold Heap.Within at hWithin ⊢
  rw [hStep.cap m]
  omega

end Verified
