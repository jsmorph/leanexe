import Project.Smalltalk.MarkMemory
import Project.Smalltalk.Loops

namespace Project.Smalltalk.Clear
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Loops

/-- The actual first loop in `collectReady`, before root marking. -/
def cleared (s : Array UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile (read s 14) ((0 : UInt64), s)
    (fun st => st.1 < read s 14) (fun st => clearNext st.2 st.1)).2

theorem clearNext_shape {s : Array UInt64} {cap : Nat} {i : UInt64}
    (hs : Shape s cap) (hi : i.toNat < cap) : Shape (clearNext s i).2 cap := by
  exact write_shape hs (cell_index_not_register hs.2.1 (successor_handle hs.2.1 hi)
    (show (1 : UInt64).toNat < 8 by decide) (show (14 : UInt64).toNat < 24 by decide))

theorem clearNext_field {s : Array UInt64} {cap : Nat} {i g k : UInt64}
    (hs : Shape s cap) (hi : i.toNat < cap) (hg : Handle cap g) (hk : k.toNat < 8) :
    field (clearNext s i).2 g k =
      if g = i + 1 ∧ k = 1 then 0 else field s g k :=
  field_write_cell hs (successor_handle hs.2.1 hi) hg (by decide) hk

theorem clearNext_register {s : Array UInt64} {cap : Nat} {i r : UInt64}
    (hs : Shape s cap) (hi : i.toNat < cap) (hr : r.toNat < 24) :
    read (clearNext s i).2 r = read s r :=
  read_write_other s _ r 0
    (cell_index_not_register hs.2.1 (successor_handle hs.2.1 hi) (by decide) hr)

theorem cleared_shape {s : Array UInt64} {cap : Nat} (hs : Shape s cap) : Shape (cleared s) cap := by
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (clearNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    exact ⟨(successor_handle hs.2.1 hi).2, clearNext_shape ht hi⟩
  exact (repeat_invariant P _ _ step (read s 14) (0, s) ⟨Nat.zero_le _, hs⟩).2

theorem cleared_register {s : Array UInt64} {cap : Nat} {r : UInt64}
    (hs : Shape s cap) (hr : r.toNat < 24) : read (cleared s) r = read s r := by
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap ∧ read st.2 r = read s r
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (clearNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht, same⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    exact ⟨(successor_handle hs.2.1 hi).2, clearNext_shape ht hi, (clearNext_register ht hi hr).trans same⟩
  exact (repeat_invariant P _ _ step (read s 14) (0, s) ⟨Nat.zero_le _, hs, rfl⟩).2.2

theorem cleared_payload {s : Array UInt64} {cap : Nat} {g k : UInt64}
    (hs : Shape s cap) (hg : Handle cap g) (hk : k.toNat < 8) (payload : k ≠ 1) :
    field (cleared s) g k = field s g k := by
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap ∧ field st.2 g k = field s g k
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (clearNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht, same⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    refine ⟨(successor_handle hs.2.1 hi).2, clearNext_shape ht hi, ?_⟩
    rw [clearNext_field ht hi hg hk]
    simp only [payload, and_false, ite_false, same]
  exact (repeat_invariant P _ _ step (read s 14) (0, s) ⟨Nat.zero_le _, hs, rfl⟩).2.2

theorem cleared_marks {s : Array UInt64} {cap : Nat} {g : UInt64}
    (hs : Shape s cap) (hg : Handle cap g) : field (cleared s) g 1 = 0 := by
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap ∧
    (g.toNat ≤ st.1.toNat → field st.2 g 1 = 0)
  have initial : P (0, s) := by
    refine ⟨Nat.zero_le _, hs, ?_⟩
    intro impossible
    have := hg.1
    simp only [UInt64.reduceToNat] at impossible
    omega
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (clearNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht, visited⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    have inc := successor_toNat (i := i) (by have := hs.2.1; omega)
    refine ⟨(successor_handle hs.2.1 hi).2, clearNext_shape ht hi, ?_⟩
    intro bound
    rw [clearNext_field ht hi hg (show (1 : UInt64).toNat < 8 by decide)]
    by_cases same : g = i + 1
    · simp only [same, and_self, ite_true]
    · simp only [same, false_and, ite_false]
      apply visited
      change g.toNat ≤ (i + 1).toNat at bound
      rw [inc] at bound
      have ne : g.toNat ≠ (i + 1).toNat := by intro eq; exact same (UInt64.toNat_inj.mp eq)
      rw [inc] at ne
      change g.toNat ≤ i.toNat
      omega
  have invariant := repeat_invariant P _ _ step (read s 14) (0, s) initial
  have endIndex := counted_index (fun t i => (clearNext t i).2) (read s 14)
    (by rw [hs.2.2.2]; exact hs.2.1) (read s 14).toNat 0 s (by simp)
  have bound : g.toNat ≤ (LeanExe.repeatWhile (read s 14) (0, s)
      (fun st => decide (st.1 < read s 14)) (fun st => clearNext st.2 st.1)).1.toNat := by
    have index : (LeanExe.repeatWhile (read s 14) (0, s)
        (fun st => decide (st.1 < read s 14)) (fun st => clearNext st.2 st.1)).1.toNat = cap := by
      simpa only [LeanExe.repeatWhile, clearNext, UInt64.reduceToNat, Nat.zero_add,
        hs.2.2.2] using endIndex
    rw [index]
    exact hg.2
  exact invariant.2.2 bound

end Project.Smalltalk.Clear
