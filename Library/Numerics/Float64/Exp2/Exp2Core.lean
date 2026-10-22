import Library.Numerics.Float64.Exp2.Exp2Selection
import Library.Numerics.Float64.Exp2.Exp2Evaluation
import Library.Numerics.Float64.Exp.ArmSpecial
import Library.Numerics.Float64.Exp.ArmScale
import LeanExe.ProofKit.RealExpError

/-!
`Exp2.exp2Core` on `Exp.expTable`.  The shifted sum's bits `ki = 0x42C8000000000000 + k` raised
by `7 · 2 ^ 52` have the form `0x4338000000000000 + k` of `exp`'s key, with the same low 19
bits, so the scale and tail words are those of `exp` for `k = 128 q + j`.  With the exact
residual `r = x - k / 128`, `2 ^ x = 2 ^ q exp (j log 2 / 128) exp (r log 2)`, and the general
reconstruction lemmas give one step on the ordinary path for `|x| ≤ 928` and on the two special
paths for `928 < x < 1024` and `-1075 < x < -928`.
-/

namespace Library.Numerics.Float64.Exp2.Exp2Core
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `exp2`'s key raised to the form of `exp`'s key. -/
def key (ki : UInt64) : UInt64 := ki + 0x0070000000000000

theorem key_toNat (ki : UInt64) (k : Int)
    (hki : (ki.toNat : Int) = (0x42C8000000000000 : Int) + k) (hk : k.natAbs ≤ 2 ^ 20) :
    ((key ki).toNat : Int) = (0x4338000000000000 : Int) + k := by
  have hkb : (k.natAbs : Int) ≤ 2 ^ 20 := by exact_mod_cast hk
  rw [← Int.abs_eq_natAbs] at hkb
  have hb := abs_le.mp hkb
  simp only [key, UInt64.toNat_add, UInt64.reduceToNat]
  omega

theorem key_mod (ki : UInt64) : key ki % 128 = ki % 128 := by
  apply UInt64.toNat_inj.mp
  simp only [key, UInt64.toNat_mod, UInt64.toNat_add, UInt64.reduceToNat]
  omega

theorem key_shift (ki : UInt64) : key ki <<< (45 : UInt64) = ki <<< (45 : UInt64) := by
  apply UInt64.toNat_inj.mp
  simp only [key, UInt64.toNat_shiftLeft, UInt64.toNat_add, UInt64.reduceToNat, Nat.reduceMod,
    Nat.shiftLeft_eq]
  omega

theorem key_scale (ki : UInt64) : Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (key ki) = Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits ki := by
  simp only [Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits, Library.Numerics.Float64.Exp.ExpScaleBits.index, key_mod, key_shift]

theorem key_index (ki : UInt64) : Library.Numerics.Float64.Exp.ExpScaleBits.index (key ki) = Library.Numerics.Float64.Exp.ExpScaleBits.index ki := by
  simp only [Library.Numerics.Float64.Exp.ExpScaleBits.index, key_mod]

/-- The sign of `k` in bit 31 of `exp2`'s key. -/
theorem sign_guard (ki : UInt64) (k : Int)
    (hki : (ki.toNat : Int) = (0x42C8000000000000 : Int) + k)
    (hkn : k.natAbs ≤ 2 ^ 30) :
    ki &&& 0x80000000 = if k < 0 then 0x80000000 else 0 := by
  have h : (k.natAbs : Int) ≤ 2 ^ 30 := by exact_mod_cast hkn
  rw [← Int.abs_eq_natAbs] at h
  have hb := abs_le.mp h
  by_cases hk : k < 0
  · have hm : ki.toNat / 2 ^ 31 % 2 = 1 := by omega
    have ht : ki.toNat.testBit 31 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hm]
      rfl
    rw [ite_eq_left hk]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.reduceToNat]
    change ki.toNat &&& 2 ^ 31 = 2 ^ 31
    rw [Nat.and_two_pow, ht]
    rfl
  · have hm : ki.toNat / 2 ^ 31 % 2 = 0 := by omega
    have ht : ki.toNat.testBit 31 = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hm]
      rfl
    rw [ite_eq_right hk]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.reduceToNat]
    change ki.toNat &&& 2 ^ 31 = 0
    rw [Nat.and_two_pow, ht]
    rfl

/-- `x + 0x1.8p52 / 128` on floats. -/
def floatShifted (x : Float) : Float := x + Float.ofBits 0x42C8000000000000

/-- `x - k / 128` on floats. -/
def floatResidual (x : Float) : Float := x - (floatShifted x - Float.ofBits 0x42C8000000000000)

/-- The table tail selected by the key. -/
def tailFloat (x : Float) : Float :=
  Float.ofBits Exp.expTable[(Library.Numerics.Float64.Exp.ExpScaleBits.index (floatShifted x).toBits).toNat]!

/-- The polynomial evaluation of `exp2Core`. -/
def tmpFloat (x : Float) : Float := Exp2Evaluation.floatEvaluation (floatResidual x) (tailFloat x)

theorem core_eq (x : Float) (special : Bool) :
    Exp2.exp2Core Exp.expTable x special =
      if special then
        Exp2.exp2SpecialCase (tmpFloat x) (Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (floatShifted x).toBits)
          (floatShifted x).toBits
      else Float.ofBits (Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (floatShifted x).toBits) +
        Float.ofBits (Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (floatShifted x).toBits) * tmpFloat x := by
  cases special <;> rfl

theorem shifted_bits (x : Float) : (floatShifted x).toBits = Exp2Selection.shifted x.toBits := by
  have hm := Exp2Selection.shift_values.1
  simp only [floatShifted, Exp2Selection.shifted, F64Bits.toBits_add, F64Bits.toBits_ofBits,
    not_nan_of_finite hm, Bool.false_eq_true, ite_false]

theorem residual_bits (x : Float) :
    (floatResidual x).toBits = Exp2Selection.residual x.toBits := by
  have hm := Exp2Selection.shift_values.1
  simp only [floatResidual, Exp2Selection.residual, Exp2Selection.selected, F64Bits.toBits_sub,
    shifted_bits, F64Bits.toBits_ofBits, not_nan_of_finite hm, Bool.false_eq_true, ite_false]

/-- The state of `exp2Core` for `|x| ≤ 1100`: the integer `k = 128 q + j` within `1/2` of
`128 x`, the exact residual, the key, and the evaluation's error. -/
theorem core_state (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| ≤ 1100) :
    ∃ (k q : Int) (j : Fin 128),
      k = 128 * q + j.val ∧ |(k : ℝ) - 128 * value x.toBits| ≤ 1 / 2 ∧ k.natAbs ≤ 2 ^ 20 ∧
      ((key (floatShifted x).toBits).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      ((key (floatShifted x).toBits) % 128).toNat = j.val ∧
      (floatShifted x).toBits &&& 0x80000000 = (if k < 0 then 0x80000000 else 0) ∧
      Finite (tmpFloat x).toBits ∧ |value (tmpFloat x).toBits| ≤ 1 / 64 ∧
      |value (tmpFloat x).toBits - (value (Library.Numerics.Float64.Exp.ExpTableBounds.tailBits j.val) +
        Real.exp ((value x.toBits - (k : ℝ) / 128) * Real.log 2) - 1)| ≤ 1 / 2 ^ 56 ∧
      |value x.toBits - (k : ℝ) / 128| ≤ 1 / 256 := by
  obtain ⟨k, hsf, hsv, hki, hke, hkn⟩ :=
    Exp2Selection.shifted_state x.toBits hxf (hx.trans (by norm_num))
  obtain ⟨hself, hselv, hselval⟩ := Exp2Selection.selected_value x.toBits k hsf hsv hkn
  obtain ⟨hrf, hrv, hrb⟩ := Exp2Selection.residual_value x.toBits k hxf hself hselv hselval hke
  have hjk := Library.Numerics.Float64.Exp.ExpShiftedBits.euclidean_index k
  let j : Fin 128 := ⟨(k % 128).toNat, hjk.1⟩
  let q := k / 128
  have hk : k = 128 * q + j.val := hjk.2
  rw [← shifted_bits] at hki
  have hkey := key_toNat _ k hki hkn
  have hj : ((key (floatShifted x).toBits) % 128).toNat = j.val :=
    Library.Numerics.Float64.Exp.ExpShiftedBits.table_remainder _ k hkey
  have hidx := (Library.Numerics.Float64.Exp.ExpScaleBits.index_values _ j hj).1
  rw [key_index] at hidx
  have htail : (tailFloat x).toBits = Library.Numerics.Float64.Exp.ExpTableBounds.tailBits j.val := by
    have htf := (Library.Numerics.Float64.Exp.ExpTableBounds.entry_bounds j).2.1
    simp only [tailFloat, F64Bits.toBits_ofBits, hidx]
    simp only [Library.Numerics.Float64.Exp.ExpTableBounds.tailBits] at htf ⊢
    simp only [not_nan_of_finite htf, Bool.false_eq_true, ite_false]
  have htb := (Library.Numerics.Float64.Exp.ExpTableBounds.entry_bounds j).2.2.2.2
  have htf := (Library.Numerics.Float64.Exp.ExpTableBounds.entry_bounds j).2.1
  have hev := Exp2Evaluation.evaluation_error _ _ hrf htf hrb htb
  have hexp := Exp2Evaluation.evaluation_exp_error _ _ hrf htf hrb htb
  have htmp : (tmpFloat x).toBits =
      Exp2Evaluation.evaluation (Exp2Selection.residual x.toBits) (Library.Numerics.Float64.Exp.ExpTableBounds.tailBits j.val) := by
    rw [tmpFloat, Exp2Evaluation.evaluation_bits, residual_bits, htail]
  rw [htmp]
  rw [hrv] at hexp hrb
  refine ⟨k, q, j, hk, hke, hkn, hkey, hj,
    sign_guard _ k hki (hkn.trans (by norm_num)), hev.1, hev.2.1, hexp, hrb⟩

/-- `2 ^ x` from the reduction. -/
theorem target_eq (a : ℝ) (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val) :
    (2 : ℝ) ^ a = (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) *
      Real.exp ((a - (k : ℝ) / 128) * Real.log 2) := by
  have h2q : (2 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 2) := by
    rw [RealExpError.exp_int_mul, Real.exp_log (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num), h2q, ← Real.exp_add, ← Real.exp_add, hk]
  congr 1
  push_cast
  ring

theorem rho_bounds (r : ℝ) (hr : |r| ≤ 1 / 256) :
    319 / 320 ≤ Real.exp (r * Real.log 2) ∧ Real.exp (r * Real.log 2) ≤ 257 / 256 := by
  have hL0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL1 := Exp2Approximation.log_two_le
  have hy : |r * Real.log 2| ≤ 7 / 2560 := by
    rw [abs_mul, abs_of_nonneg hL0]
    calc
      _ ≤ 1 / 256 * (7 / 10) := mul_le_mul hr hL1 hL0 (by norm_num)
      _ = 7 / 2560 := by norm_num
  have hl := Real.add_one_le_exp (r * Real.log 2)
  have h1 := (abs_le.mp hy).1
  have h2 := (abs_le.mp hy).2
  constructor
  · linarith
  · rcases le_or_gt (r * Real.log 2) 0 with h | h
    · have := Real.exp_le_one_iff.mpr h
      linarith
    · have hu := Real.exp_bound_div_one_sub_of_interval' h (by linarith)
      have hd : 1 / (1 - r * Real.log 2) ≤ 257 / 256 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith

#print axioms key_toNat
#print axioms key_scale
#print axioms sign_guard
#print axioms core_eq
#print axioms core_state
#print axioms target_eq
#print axioms rho_bounds

end Library.Numerics.Float64.Exp2.Exp2Core
