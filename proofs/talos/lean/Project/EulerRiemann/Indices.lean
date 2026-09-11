import LeanExe.Examples.EulerRiemann.Grid
import Init.Data.List.Range
import Init.Data.UInt.Lemmas
import Init.Omega

namespace Project.EulerRiemann.Indices
open LeanExe.Examples.EulerRiemann

theorem range_prefix (size count : Nat) (h : size ≤ count) :
    (List.range count).take size = List.range size := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_range]
    omega
  · intro i hi hj
    simp

theorem extract_prefix (values : Array UInt64) (count size : Nat)
    (hv : values.toList = (List.range count).map UInt64.ofNat)
    (hs : size ≤ count) :
    (values.extract 0 size).toList = (List.range size).map UInt64.ofNat := by
  rw [Array.toList_extract, hv]
  simp only [List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero,
    ← List.map_take, range_prefix size count hs]

theorem growIndices_toList (fuel size count : Nat) (values : Array UInt64)
    (hv : values.toList = (List.range count).map UInt64.ofNat)
    (h : size ≤ 2 ^ fuel * count) :
    (growIndices fuel size values).toList = (List.range size).map UInt64.ofNat := by
  have hlength : values.size = count := by
    have hl := congrArg List.length hv
    simpa using hl
  induction fuel generalizing count values with
  | zero =>
    exact extract_prefix values count size hv (by simpa using h)
  | succ fuel ih =>
    by_cases hs : size ≤ count
    · simpa only [growIndices, hlength, hs, ↓reduceIte] using
        extract_prefix values count size hv hs
    · simp only [growIndices, hlength, hs, ↓reduceIte, Nat.toUInt64_eq]
      apply ih (count + count)
      · rw [Array.toList_append, Array.toList_map, hv]
        have hmap :
            ((List.range count).map UInt64.ofNat).map
              (fun i => i + UInt64.ofNat count) =
            ((List.range count).map (fun i => count + i)).map UInt64.ofNat := by
          simp only [List.map_map, Function.comp_def, UInt64.ofNat_add]
          congr 1
          funext i
          exact UInt64.add_comm _ _
        rw [hmap, ← List.map_append, ← List.range_add]
      · simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.two_mul, Nat.mul_add] using h
      · simp [hlength]

theorem indices_toList (fuel size : Nat) (h : size ≤ 2 ^ fuel) :
    (indices fuel size).toList = (List.range size).map UInt64.ofNat := by
  exact growIndices_toList fuel size 1 #[0] rfl (by simpa using h)

theorem gridIndices_toList (n : Nat) (hn : validSize n = true) :
    (gridIndices n).toList = (List.range (n * n)).map UInt64.ofNat := by
  have hu : n ≤ 800 := (of_decide_eq_true hn).2
  have htotal : n * n ≤ 800 * 800 := Nat.mul_le_mul hu hu
  simp only [gridIndices, hn, ↓reduceIte]
  exact indices_toList 20 (n * n) (by omega)

theorem gridIndices_size (n : Nat) (hn : validSize n = true) :
    (gridIndices n).size = n * n := by
  simpa using congrArg List.length (gridIndices_toList n hn)

#print axioms indices_toList
#print axioms gridIndices_toList

end Project.EulerRiemann.Indices
