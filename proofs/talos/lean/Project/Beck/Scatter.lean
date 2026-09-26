import Project.Beck.MatrixBasis

namespace Project.Beck.Scatter

open LeanExe.Examples.Beck

def write (xs : List Nat) (index : Nat → Nat) (value : Nat → UInt64) (a : Array UInt64) :
    Array UInt64 := xs.foldl (fun a j => a.set! (index j) (value j)) a

theorem size (xs : List Nat) (index : Nat → Nat) (value : Nat → UInt64) (a : Array UInt64) :
    (write xs index value a).size = a.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons j xs ih => simpa [write, List.foldl_cons] using ih (a.set! (index j) (value j))

theorem untouched (xs : List Nat) (index : Nat → Nat) (value : Nat → UInt64) (a : Array UInt64)
    (i : Nat) (fresh : ∀ j ∈ xs, i ≠ index j) :
    (write xs index value a)[i]! = a[i]! := by
  induction xs generalizing a with
  | nil => rfl
  | cons j xs ih =>
    change (write xs index value (a.set! (index j) (value j)))[i]! = _
    rw [ih _ (by intro k hk; exact fresh k (by simp [hk]))]
    exact Array.getElem!_set!_ne a (index j) i (value j) (Ne.symm (fresh j (by simp)))

theorem written (xs : List Nat) (index : Nat → Nat) (value : Nat → UInt64) (a : Array UInt64)
    (distinct : (xs.map index).Nodup) (bounded : ∀ j ∈ xs, index j < a.size)
    (j : Nat) (member : j ∈ xs) :
    (write xs index value a)[index j]! = value j := by
  induction xs generalizing a with
  | nil => simp at member
  | cons k xs ih =>
    have nodup : (xs.map index).Nodup := (List.nodup_cons.mp distinct).2
    have fresh : index k ∉ xs.map index := (List.nodup_cons.mp distinct).1
    change (write xs index value (a.set! (index k) (value k)))[index j]! = _
    rcases List.mem_cons.mp member with rfl | member
    · rw [untouched _ _ _ _ _ (by
        intro l hl e
        exact fresh (List.mem_map.mpr ⟨l, hl, e.symm⟩))]
      exact Array.getElem!_set!_self a (index j) (value j) (bounded j (by simp))
    · apply ih _ nodup _ member
      intro l hl
      simpa using bounded l (by simp [hl])

end Project.Beck.Scatter
