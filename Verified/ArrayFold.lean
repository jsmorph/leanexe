import Verified.State

namespace Verified

open LeanExe.ProofKit LeanExe.Pipeline Wasm

private theorem array_fold_prefix [Inhabited α] (xs : Array α) (step : β → α → β)
    (init : β) (n : Nat) (hn : n ≤ xs.size) :
    Nat.fold n (fun i _ acc => step acc xs[i]!) init =
      ArrayFold.foldPrefix xs step init n := by
  induction n with
  | zero => simp [ArrayFold.foldPrefix]
  | succ n ih =>
    rw [Nat.fold_succ, ih (by omega), ArrayFold.foldPrefix_succ xs step init n (by omega)]
    rw [getElem!_pos xs n (by omega)]

theorem array_fold_eq_loop [Inhabited α] (xs : Array α) (step : β → α → β)
    (init : β) (hSize : xs.size < UInt64.size) :
    xs.foldl step init = LeanExe.loop xs.size.toUInt64 init
      (fun i acc => step acc xs[i.toNat]!) := by
  unfold LeanExe.loop
  rw [UInt64.toNat_ofNat_of_lt' hSize]
  have hIndices :
      (fun (i : Nat) (_ : i < xs.size) (acc : β) => step acc xs[(UInt64.ofNat i).toNat]!) =
        (fun (i : Nat) (_ : i < xs.size) (acc : β) => step acc xs[i]!) := by
    funext i hi acc
    rw [UInt64.toNat_ofNat_of_lt' (hi.trans hSize)]
  rw [hIndices, array_fold_prefix xs step init xs.size (Nat.le_refl _),
    ArrayFold.foldPrefix_size]

theorem Ty.Rep.array_size_lt {mode : Mode} {heap : Heap} {store : Store Unit}
    {e : Elem} {ws : List Value} {xs : Array e.denote}
    (h : Ty.Rep mode heap store (.array e) ws xs) : xs.size < UInt64.size := by
  obtain ⟨ptr, -, hArray⟩ := h
  have hWords := hArray.borrow.values.size_lt
  rw [Elem.words_size] at hWords
  exact (Nat.le_mul_of_pos_right xs.size e.width_pos).trans_lt hWords

theorem Ty.Rep.array_fold_eq_loop {mode : Mode} {heap : Heap} {store : Store Unit}
    {e : Elem} {ws : List Value} {xs : Array e.denote}
    (h : Ty.Rep mode heap store (.array e) ws xs) (step : β → e.denote → β) (init : β) :
    xs.foldl step init = LeanExe.loop xs.size.toUInt64 init
      (fun i acc => step acc xs[i.toNat]!) :=
  Verified.array_fold_eq_loop xs step init h.array_size_lt

#print axioms array_fold_eq_loop
#print axioms Ty.Rep.array_size_lt
#print axioms Ty.Rep.array_fold_eq_loop

end Verified
