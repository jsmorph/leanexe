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

theorem Env.pot_treeFields {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ)
    (shape : TreeShape) (words : Fin shape.words → UInt64)
    (children : Fin shape.children → Tree shape) (base : Nat) (mode : Mode)
    (slots : List Slot) (sel : Nat → Bool) :
    (Env.treeFields shape words children env).pot store s (shape.slots base mode slots) sel =
      env.pot store s slots (fun i => sel (i + shape.bindCount)) := by
  change (if sel 0 then 0 else 0) +
    (Env.prependRepeat .word shape.words words
      (Env.prependRepeat (.tree shape) shape.children children env)).pot store s
      (((List.range shape.words).map (fun i => Slot.mk (base + 1 + i) .borrowed)) ++
        (((List.range shape.children).map (fun i => Slot.mk (base + 1 + shape.words + i) mode)) ++
          slots)) (fun i => sel (i + 1)) = _
  simp only [ite_self, Nat.zero_add]
  rw [Env.pot_repeatZero store s _ .word (fun _ _ => rfl) shape.words words
    ((List.range shape.words).map (fun i => Slot.mk (base + 1 + i) .borrowed)) _
    (fun i => sel (i + 1)) (by simp)]
  rw [Env.pot_repeatZero store s env (.tree shape) (fun _ _ => rfl) shape.children children
    ((List.range shape.children).map (fun i => Slot.mk (base + 1 + shape.words + i) mode)) slots
    (fun i => sel (i + shape.words + 1)) (by simp)]
  congr 1
  funext i
  congr 1
  simp only [TreeShape.bindCount]
  omega

theorem TreeShape.slots_getD_suffix (shape : TreeShape) (base : Nat) (mode : Mode)
    (slots : List Slot) (i : Nat) :
    (shape.slots base mode slots).getD (i + shape.bindCount) default = slots.getD i default := by
  rw [shape.slots_append]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [shape.slots_length]; omega), shape.slots_length,
    Nat.add_sub_cancel_right]

theorem dyingPot_treeFields {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ)
    (shape : TreeShape) (words : Fin shape.words → UInt64)
    (children : Fin shape.children → Tree shape) (base : Nat) (mode : Mode)
    (slots : List Slot) (paid : List Bool) (L0 L1 : Nat → Bool) :
    dyingPot store s (Env.treeFields shape words children env) (shape.slots base mode slots)
      (List.replicate shape.bindCount false ++ paid) L0 L1 =
      dyingPot store s env slots paid (fun i => L0 (i + shape.bindCount))
        (fun i => L1 (i + shape.bindCount)) := by
  unfold dyingPot
  rw [Env.pot_treeFields]
  apply Env.pot_ext
  intro i _
  rw [shape.slots_getD_suffix]
  simp only [paidAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.length_replicate,
    Nat.add_sub_cancel_right]

theorem dyingPot_treeEntry {Γ : List Ty} (store : Store Unit) (s : Locals) (env : Env Γ)
    (shape : TreeShape) (words : Fin shape.words → UInt64)
    (children : Fin shape.children → Tree shape) (base : Nat) (mode : Mode)
    (slots : List Slot) (paid : List Bool) (L1 live : Nat → Bool) :
    dyingPot store s (Env.treeFields shape words children env) (shape.slots base mode slots)
      (List.replicate shape.bindCount false ++ paid)
      (fun i => decide (i < shape.bindCount) || shift shape.bindCount L1 i)
      (shift shape.bindCount live) = dyingPot store s env slots paid L1 live := by
  rw [dyingPot_treeFields]
  apply dyingPot_congr <;> intro i <;>
    simp [shift, show ¬i + shape.bindCount < shape.bindCount by omega]

theorem treeCase_bodyWithin {Γ : List Ty} {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {L0 L1 live : Nat → Bool} {base fieldBase : Nat} {shape : TreeShape} {mode : Mode}
    {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
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
      (dyingPot store s (Env.treeFields shape words children env)
        (shape.slots fieldBase mode slots) (List.replicate shape.bindCount false ++ paid)
        (fun i => decide (i < shape.bindCount) || shift shape.bindCount L1 i)
        (shift shape.bindCount live) + bodyCost) := by
  rw [dyingPot_treeEntry, dyingPot_step h0 hStep hFrame hL1 L1 live (fun _ hi => hi)]
  have hSplit := dyingPot_split (store := store0) (s := s0) (env := env) (slots := slots)
    (paid := paid) L0 L1 live hL1 hLive
  unfold Heap.Within at hWithin ⊢
  rw [hStep.cap m]
  omega

end Verified
