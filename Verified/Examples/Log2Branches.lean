import Verified.Examples.Log2
import Verified.Examples.LogBranches

/-!
The paths of `Log2.log2With` by the bits of the argument.  The guards are those of `Log.logWith`
except the path near 1, which runs from `0x3FEEA4AF00000000` to below `0x3FF0B55900000000`, the
words of `1 - 0x1.5b51p-5` and `1 + 0x1.6ab2p-5`.  The other guard lemmas come from
`LogBranches`.
-/

namespace Verified.Examples.Log2Branches
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem near2_guard (ix : UInt64) :
    ix - 4606800540372828160 < 4607381812656734208 - 4606800540372828160 ↔
      4606800540372828160 ≤ ix.toNat ∧ ix.toNat < 4607381812656734208 := by
  have hix := ix.toNat_lt
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_sub]
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

theorem near_selected (tab tab2 : Array UInt64) (x : Float)
    (hlo : 4606800540372828160 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 4607381812656734208)
    (hne : x.toBits.toNat ≠ 4607182418800017408) :
    Log2.log2With tab tab2 x = Log2.log2Near1 x := by
  have hg := (near2_guard x.toBits).mpr ⟨hlo, hhi⟩
  have h1 : ¬ (x.toBits == 4607182418800017408) = true := by
    rw [LogBranches.word_guard]
    exact hne
  simp only [Log2.log2With]
  rw [ite_eq_left hg, ite_eq_right h1]

theorem one_selected (tab tab2 : Array UInt64) (x : Float)
    (h : x.toBits.toNat = 4607182418800017408) :
    Log2.log2With tab tab2 x = 0.0 := by
  have hg := (near2_guard x.toBits).mpr ⟨by omega, by omega⟩
  have h1 : (x.toBits == 4607182418800017408) = true := by
    rw [LogBranches.word_guard]
    exact h
  simp only [Log2.log2With]
  rw [ite_eq_left hg, ite_eq_left h1]

/-- A positive normal argument outside the path near 1 takes the main path. -/
theorem normal_selected (tab tab2 : Array UInt64) (x : Float)
    (hlo : 4503599627370496 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 9218868437227405312)
    (hnear : x.toBits.toNat < 4606800540372828160 ∨ 4607381812656734208 ≤ x.toBits.toNat) :
    Log2.log2With tab tab2 x = Log2.log2Core tab tab2 x.toBits := by
  have hg : ¬ x.toBits - 4606800540372828160 < 4607381812656734208 - 4606800540372828160 := by
    rw [near2_guard]
    omega
  have ht : ¬ x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [LogBranches.top_guard]
    omega
  simp only [Log2.log2With]
  rw [ite_eq_right hg, ite_eq_right ht]

/-- A positive subnormal argument is scaled by `2 ^ 52` and takes the main path. -/
theorem subnormal_selected (tab tab2 : Array UInt64) (x : Float)
    (hlo : 0 < x.toBits.toNat) (hhi : x.toBits.toNat < 4503599627370496) :
    Log2.log2With tab tab2 x =
      Log2.log2Core tab tab2 ((x * Float.ofBits 4841369599423283200).toBits - (52 : UInt64) <<< 52) := by
  have hg : ¬ x.toBits - 4606800540372828160 < 4607381812656734208 - 4606800540372828160 := by
    rw [near2_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [LogBranches.top_guard]
    omega
  have hd : ¬ (x.toBits * 2 == 0) = true := by
    rw [LogBranches.double_guard]
    omega
  have hi : ¬ (x.toBits == 9218868437227405312) = true := by
    rw [LogBranches.word_guard]
    simp only [UInt64.reduceToNat]
    omega
  have hs := LogBranches.small_top x.toBits hhi
  simp only [Log2.log2With]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_right hd, ite_eq_right hi, hs, ite_eq_right Bool.false_ne_true]

theorem zero_selected (tab tab2 : Array UInt64) (x : Float)
    (h : x.toBits.toNat % 9223372036854775808 = 0) :
    Log2.log2With tab tab2 x = -1.0 / 0.0 := by
  have hg : ¬ x.toBits - 4606800540372828160 < 4607381812656734208 - 4606800540372828160 := by
    rw [near2_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [LogBranches.top_guard]
    omega
  have hd : (x.toBits * 2 == 0) = true := (LogBranches.double_guard _).mpr h
  simp only [Log2.log2With]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_left hd]

theorem infinity_selected (tab tab2 : Array UInt64) (x : Float)
    (h : x.toBits.toNat = 9218868437227405312) :
    Log2.log2With tab tab2 x = x := by
  have hg : ¬ x.toBits - 4606800540372828160 < 4607381812656734208 - 4606800540372828160 := by
    rw [near2_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [LogBranches.top_guard]
    omega
  have hd : ¬ (x.toBits * 2 == 0) = true := by
    rw [LogBranches.double_guard]
    omega
  have hi : (x.toBits == 9218868437227405312) = true := by
    rw [LogBranches.word_guard]
    exact h
  simp only [Log2.log2With]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_right hd, ite_eq_left hi]

/-- A negative argument other than `-0`, or a positive NaN pattern, takes the invalid path. -/
theorem invalid_selected (tab tab2 : Array UInt64) (x : Float)
    (h : (9223372036854775808 ≤ x.toBits.toNat ∧ x.toBits.toNat ≠ 9223372036854775808) ∨
      (9218868437227405312 < x.toBits.toNat ∧ x.toBits.toNat < 9223372036854775808)) :
    Log2.log2With tab tab2 x = (x - x) / (x - x) := by
  have hix := x.toBits.toNat_lt
  have hg : ¬ x.toBits - 4606800540372828160 < 4607381812656734208 - 4606800540372828160 := by
    rw [near2_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [LogBranches.top_guard]
    omega
  have hd : ¬ (x.toBits * 2 == 0) = true := by
    rw [LogBranches.double_guard]
    omega
  have hi : ¬ (x.toBits == 9218868437227405312) = true := by
    rw [LogBranches.word_guard]
    simp only [UInt64.reduceToNat]
    omega
  have hs : (x.toBits >>> 48 &&& 32768 != 0 || x.toBits >>> 48 &&& 32752 == 32752) = true := by
    rcases h with h | h
    · exact LogBranches.negative_top _ h.1
    · exact LogBranches.nan_top _ h.1 h.2
  simp only [Log2.log2With]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_right hd, ite_eq_right hi, ite_eq_left hs]

#print axioms near2_guard
#print axioms near_selected
#print axioms one_selected
#print axioms normal_selected
#print axioms subnormal_selected
#print axioms zero_selected
#print axioms infinity_selected
#print axioms invalid_selected

end Verified.Examples.Log2Branches
