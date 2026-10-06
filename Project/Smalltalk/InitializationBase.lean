import Project.Smalltalk.Heap
import Project.Smalltalk.Loops

namespace Project.Smalltalk.InitializationBase
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory

def capacity (requested : UInt64) : UInt64 := max 8 (min requested 1048576)

theorem capacity_bounds (requested : UInt64) :
    8 ≤ (capacity requested).toNat ∧ (capacity requested).toNat ≤ 1048576 := by
  change (fun cap : UInt64 => 8 ≤ cap.toNat ∧ cap.toNat ≤ 1048576)
    (if (8 : UInt64) ≤ (if requested ≤ 1048576 then requested else 1048576) then
      (if requested ≤ 1048576 then requested else 1048576) else 8)
  by_cases small : requested ≤ 1048576
  · by_cases large : (8 : UInt64) ≤ requested
    · simp only [small, large, ite_true]
      exact ⟨UInt64.le_iff_toNat_le.mp large, UInt64.le_iff_toNat_le.mp small⟩
    · simp only [small, large, ite_true, ite_false, UInt64.reduceToNat]
      decide
  · simp only [small, ite_false]
    decide

def headers (cap stress : UInt64) : Array UInt64 :=
  let s := LeanExe.build (24 + 9 * cap) fun _ => (0 : UInt64)
  write (write (write (write (write s 14 cap) 12 stress) 8 4) 9 (cap - 3)) 13 3

theorem arenaSize {cap : UInt64} (bound : cap.toNat ≤ 1048576) :
    (24 + 9 * cap).toNat = 24 + 9 * cap.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  have mult : 9 * cap.toNat < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt mult, Nat.mod_eq_of_lt (by omega)]

theorem headers_size (cap stress : UInt64) : (headers cap stress).size = (24 + 9 * cap).toNat := by
  simp only [headers, write_size, LeanExe.build, Array.size_ofFn]

theorem zero_read (cap j : UInt64) : read (LeanExe.build (24 + 9 * cap) (fun _ => (0 : UInt64))) j = 0 := by
  let zeros : Array UInt64 := Array.ofFn (n := (24 + 9 * cap).toNat) fun _ => 0
  change zeros[j.toNat]! = 0
  by_cases bound : j.toNat < (24 + 9 * cap).toNat
  · have inside : j.toNat < zeros.size := by simpa only [zeros, Array.size_ofFn] using bound
    rw [getElem!_pos zeros j.toNat inside]
    exact Array.getElem_ofFn inside
  · have outside : ¬j.toNat < zeros.size := by simpa only [zeros, Array.size_ofFn] using bound
    exact getElem!_neg zeros j.toNat outside

theorem headers_read {cap : UInt64} (bound : cap.toNat ≤ 1048576) (stress j : UInt64) :
    read (headers cap stress) j =
      if j = 13 then 3 else if j = 9 then cap - 3 else if j = 8 then 4 else
      if j = 12 then stress else if j = 14 then cap else 0 := by
  have size := arenaSize bound
  have rbound : ∀ r : UInt64, r.toNat < 24 → r.toNat < (24 + 9 * cap).toNat := by
    intro r hr; rw [size]; omega
  simp only [headers, read_write, write_size, LeanExe.build, Array.size_ofFn,
    rbound 14 (by decide), rbound 12 (by decide), rbound 8 (by decide),
    rbound 9 (by decide), rbound 13 (by decide)]
  rw [show read (Array.ofFn fun _ : Fin (24 + 9 * cap).toNat => (0 : UInt64)) j = 0
    from zero_read cap j]

theorem headers_shape {cap : UInt64} (lower : 8 ≤ cap.toNat) (upper : cap.toNat ≤ 1048576)
    (stress : UInt64) : Shape (headers cap stress) cap.toNat := by
  refine ⟨lower, upper, ?_, ?_⟩
  · rw [headers_size, arenaSize upper]
  · rw [headers_read upper]
    simp

theorem headers_field {cap : UInt64} (upper : cap.toNat ≤ 1048576)
    (stress : UInt64) {h k : UInt64} (handle : Handle cap.toNat h) (bound : k.toNat < 8) :
    field (headers cap stress) h k = 0 := by
  rw [field, headers_read upper]
  simp only [cell_index_not_register upper handle bound (show (13 : UInt64).toNat < 24 by decide),
    cell_index_not_register upper handle bound (show (9 : UInt64).toNat < 24 by decide),
    cell_index_not_register upper handle bound (show (8 : UInt64).toNat < 24 by decide),
    cell_index_not_register upper handle bound (show (12 : UInt64).toNat < 24 by decide),
    cell_index_not_register upper handle bound (show (14 : UInt64).toNat < 24 by decide), ite_false]

end Project.Smalltalk.InitializationBase
