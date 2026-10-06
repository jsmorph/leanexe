import LeanExe.Smalltalk.Runtime
import Init.Data.Array.Lemmas
import Lean.Elab.Tactic.Omega

/-! Facts about the array operations used by the Smalltalk VM and collector.
The statements refer to the executable definitions in `LeanExe.Smalltalk`. -/
namespace Project.Smalltalk.Memory
open LeanExe.Smalltalk.Arena

@[simp] theorem write_size (s : Array UInt64) (i v : UInt64) :
    (write s i v).size = s.size := Array.size_set! ..

@[simp] theorem read_write_same (s : Array UInt64) (i v : UInt64)
    (hi : i.toNat < s.size) : read (write s i v) i = v :=
  Array.getElem!_set!_self s i.toNat v hi

theorem read_write_other (s : Array UInt64) (i j v : UInt64)
    (hij : i ≠ j) : read (write s i v) j = read s j := by
  apply Array.getElem!_set!_ne
  intro eq
  apply hij
  exact UInt64.toNat_inj.mp eq

theorem read_write (s : Array UInt64) (i j v : UInt64)
    (hi : i.toNat < s.size) :
    read (write s i v) j = if j = i then v else read s j := by
  by_cases h : j = i
  · subst j; simp [hi]
  · simp [h, read_write_other s i j v (Ne.symm h)]

def Shape (s : Array UInt64) (cap : Nat) : Prop :=
  8 ≤ cap ∧ cap ≤ 1048576 ∧ s.size = 24 + 9 * cap ∧ (read s 14).toNat = cap

def Handle (cap : Nat) (h : UInt64) : Prop := 1 ≤ h.toNat ∧ h.toNat ≤ cap

theorem register_bound {s : Array UInt64} {cap : Nat} {r : UInt64}
    (hs : Shape s cap) (hr : r.toNat < 24) : r.toNat < s.size := by
  rw [hs.2.2.1]
  omega

theorem address_toNat {cap : Nat} {h : UInt64}
    (hc : cap ≤ 1048576) (hh : Handle cap h) :
    (address h).toNat = 24 + 8 * (h.toNat - 1) := by
  have one : (1 : UInt64) ≤ h := by
    simpa only [UInt64.le_iff_toNat_le, UInt64.reduceToNat] using hh.1
  have hBound := hh.2
  simp only [address, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_sub_of_le _ _ one, UInt64.reduceToNat]
  have small : 8 * (h.toNat - 1) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega)]

theorem cell_index_toNat {cap : Nat} {h k : UInt64}
    (hc : cap ≤ 1048576) (hh : Handle cap h) (hk : k.toNat < 8) :
    (address h + k).toNat = 24 + 8 * (h.toNat - 1) + k.toNat := by
  have hBound := hh.2
  rw [UInt64.toNat_add, address_toNat hc hh, Nat.mod_eq_of_lt (by omega)]

theorem cell_index_bound {s : Array UInt64} {cap : Nat} {h k : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (hk : k.toNat < 8) :
    (address h + k).toNat < s.size := by
  rw [cell_index_toNat hs.2.1 hh hk, hs.2.2.1]
  have := hh.1
  have := hh.2
  omega

theorem cell_index_not_register {cap : Nat} {h k r : UInt64}
    (hc : cap ≤ 1048576) (hh : Handle cap h) (hk : k.toNat < 8)
    (hr : r.toNat < 24) : address h + k ≠ r := by
  intro eq
  have := congrArg UInt64.toNat eq
  rw [cell_index_toNat hc hh hk] at this
  omega

theorem cell_indices_distinct {cap : Nat} {h g k j : UInt64}
    (hc : cap ≤ 1048576) (hh : Handle cap h) (hg : Handle cap g)
    (hk : k.toNat < 8) (hj : j.toNat < 8) (different : h ≠ g ∨ k ≠ j) :
    address h + k ≠ address g + j := by
  intro eq
  have same := congrArg UInt64.toNat eq
  rw [cell_index_toNat hc hh hk, cell_index_toNat hc hg hj] at same
  have hh1 := hh.1
  have hg1 := hg.1
  have hgEq : h.toNat = g.toNat := by omega
  have hkEq : k.toNat = j.toNat := by omega
  cases different with
  | inl ne => exact ne (UInt64.toNat_inj.mp hgEq)
  | inr ne => exact ne (UInt64.toNat_inj.mp hkEq)

theorem cell_index_eq_iff {cap : Nat} {h g k j : UInt64}
    (hc : cap ≤ 1048576) (hh : Handle cap h) (hg : Handle cap g)
    (hk : k.toNat < 8) (hj : j.toNat < 8) :
    address h + k = address g + j ↔ h = g ∧ k = j := by
  constructor
  · intro eq
    by_cases hEq : h = g
    · refine ⟨hEq, ?_⟩
      by_cases kEq : k = j
      · exact kEq
      · exact False.elim (cell_indices_distinct hc hh hg hk hj (Or.inr kEq) eq)
    · exact False.elim (cell_indices_distinct hc hh hg hk hj (Or.inl hEq) eq)
  · rintro ⟨rfl, rfl⟩; rfl

theorem write_shape {s : Array UInt64} {cap : Nat} {i v : UInt64}
    (hs : Shape s cap) (hi : i ≠ 14) : Shape (write s i v) cap := by
  exact ⟨hs.1, hs.2.1, by simpa using hs.2.2.1,
    by simpa [read_write_other s i 14 v hi] using hs.2.2.2⟩

theorem field_write_register {s : Array UInt64} {cap : Nat} {h k r v : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (hk : k.toNat < 8)
    (hr : r.toNat < 24) : field (write s r v) h k = field s h k :=
  read_write_other s r (address h + k) v
    (Ne.symm (cell_index_not_register hs.2.1 hh hk hr))

theorem field_write_cell {s : Array UInt64} {cap : Nat} {h g k j v : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (hg : Handle cap g)
    (hk : k.toNat < 8) (hj : j.toNat < 8) :
    field (write s (address h + k) v) g j =
      if g = h ∧ j = k then v else field s g j := by
  by_cases eq : g = h ∧ j = k
  · rcases eq with ⟨rfl, rfl⟩
    simp only [field, and_self, ite_true]
    exact read_write_same _ _ _ (cell_index_bound hs hg hj)
  · have ne : h ≠ g ∨ k ≠ j := by
      by_cases hEq : h = g
      · right; intro kEq; exact eq ⟨hEq.symm, kEq.symm⟩
      · exact Or.inl hEq
    simp [eq, field, read_write_other _ _ _ _
      (cell_indices_distinct hs.2.1 hh hg hk hj ne)]

@[simp] theorem fail_size (s : Array UInt64) (reason : UInt64) :
    (fail s reason).size = s.size := by simp only [fail, write_size]

theorem fail_read {s : Array UInt64} {cap : Nat} (hs : Shape s cap)
    (reason j : UInt64) :
    read (fail s reason) j = if j = 15 then reason else if j = 0 then 4 else read s j := by
  have h0 := register_bound hs (show (0 : UInt64).toNat < 24 by decide)
  have h15 := register_bound hs (show (15 : UInt64).toNat < 24 by decide)
  simp only [fail, read_write, write_size, h0, h15]

theorem successor_toNat {i : UInt64} (hi : i.toNat < 1048576) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem successor_handle {cap : Nat} {i : UInt64}
    (hc : cap ≤ 1048576) (hi : i.toNat < cap) : Handle cap (i + 1) := by
  have bound : i.toNat < 1048576 := by omega
  simp only [Handle, successor_toNat bound]
  omega

theorem kind_eq_field {s : Array UInt64} {cap : Nat} {h : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) : kind s h = field s h 0 := by
  have nonzero : h ≠ 0 := by
    intro zero
    have positive := hh.1
    rw [zero] at positive
    exact (by decide : ¬ 1 ≤ (0 : UInt64).toNat) positive
  have within : ¬ read s 14 < h := by
    simp only [UInt64.lt_iff_toNat_lt, hs.2.2.2]
    have := hh.2
    omega
  simp only [kind, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, nonzero, within,
    false_or, ite_false]

theorem work_index_toNat {s : Array UInt64} {cap : Nat} {n : UInt64}
    (hs : Shape s cap) (hn : n.toNat ≤ cap) :
    (24 + 8 * read s 14 + n).toNat = 24 + 8 * cap + n.toNat := by
  have mult : (8 * read s 14).toNat = 8 * cap := by
    rw [UInt64.toNat_mul, hs.2.2.2]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    have := hs.2.1
    omega
  have base : (24 + 8 * read s 14).toNat = 24 + 8 * cap := by
    rw [UInt64.toNat_add, mult]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    have := hs.2.1
    omega
  rw [UInt64.toNat_add, base]
  apply Nat.mod_eq_of_lt
  have := hs.2.1
  omega

theorem work_index_bound {s : Array UInt64} {cap : Nat} {n : UInt64}
    (hs : Shape s cap) (hn : n.toNat < cap) :
    (24 + 8 * read s 14 + n).toNat < s.size := by
  rw [work_index_toNat hs (by omega), hs.2.2.1]
  omega

theorem work_index_not_register {s : Array UInt64} {cap : Nat} {n r : UInt64}
    (hs : Shape s cap) (hn : n.toNat ≤ cap) (hr : r.toNat < 24) :
    24 + 8 * read s 14 + n ≠ r := by
  intro eq
  have same := congrArg UInt64.toNat eq
  rw [work_index_toNat hs hn] at same
  omega

theorem work_index_not_cell {s : Array UInt64} {cap : Nat} {n h k : UInt64}
    (hs : Shape s cap) (hn : n.toNat ≤ cap) (hh : Handle cap h) (hk : k.toNat < 8) :
    24 + 8 * read s 14 + n ≠ address h + k := by
  intro eq
  have same := congrArg UInt64.toNat eq
  rw [work_index_toNat hs hn, cell_index_toNat hs.2.1 hh hk] at same
  have := hh.1
  have := hh.2
  omega

theorem work_index_eq_iff {s : Array UInt64} {cap : Nat} {n m : UInt64}
    (hs : Shape s cap) (hn : n.toNat ≤ cap) (hm : m.toNat ≤ cap) :
    24 + 8 * read s 14 + n = 24 + 8 * read s 14 + m ↔ n = m := by
  constructor
  · intro eq
    have same := congrArg UInt64.toNat eq
    rw [work_index_toNat hs hn, work_index_toNat hs hm] at same
    apply UInt64.toNat_inj.mp
    omega
  · intro eq; rw [eq]

end Project.Smalltalk.Memory
