import Library.Arrays.Search.Proof
import Examples.RemoveZero.Program
import Examples.RemoveZero.Spec
import LeanExe.IR.Combinators

/-! The program equals the specification, a fact about the Lean definitions that the theorems of
both compilers use. -/

namespace Examples.RemoveZero

open LeanExe.IR Library.Arrays.Search

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  by_cases hs : xs.size ≤ 8
  · have hle : xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_true, hs]
    rcases firstZero_cases xs xs.size.toUInt64 with ⟨hk, hnz⟩ | ⟨j, hj, hk, hz, hb⟩
    · rw [hn] at hnz
      have hnone : xs.findIdx? (fun element => element == (0 : UInt64)) = none := by
        refine Array.findIdx?_eq_none_iff.mpr fun x hx => ?_
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
        have := hnz i hi
        rw [getElem!_pos xs i hi] at this
        simpa using this
      have hnn : ¬ xs.size.toUInt64 < xs.size.toUInt64 := by simp
      rw [hnone, hk]
      simp only [hnn, ite_false]
      apply Array.ext
      · rw [build_size, hn]
      · intro i hi _
        rw [build_size, hn] at hi
        have hit : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi h)
        have hlt : UInt64.ofNat i < xs.size.toUInt64 := by
          rw [UInt64.lt_iff_toNat_lt, hit, hn]; exact hi
        rw [← getElem!_pos (LeanExe.build _ _) i (by rw [build_size, hn]; exact hi),
          build_get (by rw [hn]; exact hi)]
        simp only [hlt, ite_true, hit]
        exact getElem!_pos xs i hi
    · rw [hn] at hj
      have hjs : j < xs.size := hj
      have hsome : xs.findIdx? (fun element => element == (0 : UInt64)) = some j := by
        refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨hjs, ?_, fun i hi => ?_⟩
        · rw [← getElem!_pos xs j hjs, hz]; rfl
        · have := hb i hi
          rw [getElem!_pos xs i (by omega)] at this
          simpa using this
      have hjt : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hjs h)
      have hklt : Library.Arrays.Search.firstZero xs xs.size.toUInt64 < xs.size.toUInt64 := by
        rw [hk, UInt64.lt_iff_toNat_lt, hjt, hn]; exact hjs
      have hm : (xs.size.toUInt64 - 1).toNat = xs.size - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]; rfl
      rw [hsome]
      simp only [hklt, ite_true, Array.eraseIdx!, hjs, dite_true]
      apply Array.ext
      · rw [build_size, hm, Array.size_eraseIdx]
      · intro i hi hi'
        rw [build_size, hm] at hi
        have hit : (UInt64.ofNat i).toNat = i :=
          UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (by omega : i < xs.size) h)
        rw [← getElem!_pos (LeanExe.build _ _) i (by rw [build_size, hm]; exact hi),
          build_get (by rw [hm]; exact hi), Array.getElem_eraseIdx]
        have hlt : UInt64.ofNat i < Library.Arrays.Search.firstZero xs xs.size.toUInt64 ↔ i < j := by
          rw [hk, UInt64.lt_iff_toNat_lt, hit, hjt]
        by_cases hij : i < j
        · simp only [hlt.mpr hij, ite_true, hit, hij, dite_true]
          exact getElem!_pos xs i (by omega)
        · simp only [show ¬ UInt64.ofNat i < Library.Arrays.Search.firstZero xs xs.size.toUInt64 from
            fun h' => hij (hlt.mp h'), ite_false, hij, dite_false]
          have : (UInt64.ofNat i + 1).toNat = i + 1 := by
            rw [UInt64.toNat_add, hit]; simp; omega
          rw [this]
          exact getElem!_pos xs (i + 1) (by omega)
  · have hle : ¬ xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_false, hs]
    rfl

end Examples.RemoveZero
