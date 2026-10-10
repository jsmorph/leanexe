import Verified.Examples.Exp10Reduction
import Verified.Examples.ArmSpecial
import Verified.Examples.ArmScale
import Verified.Examples.Exp2Paths

/-!
`Exp2.exp10Core` on `Exp.expTable`.  Its key is that of `exp`, so the scale and tail words are
`exp`'s for `k = 128 q + j`.  With the ideal residual `x - k ratio`,
`10 ^ x = 2 ^ q exp (j log 2 / 128) exp ((x - k ratio) log 10)`, and the computed residual is
within `2 ^ -61` of the ideal one, so the evaluation approximates `T + ρ - 1` for
`ρ = exp ((x - k ratio) log 10)` within `2 ^ -56`.  The general reconstruction lemmas then give
one step on the ordinary path for `|x| < 256` and on the special paths for
`256 ≤ x ≤ 0x1.34413509f79fep8` and `-350 ≤ x ≤ -256`.
-/

namespace Verified.Examples.Exp10Core
open CodeLib.IEEE64
open LeanExe.ProofKit Exp10Constants Exp10Reduction

set_option exponentiation.threshold 4096

/-- `x · 128 / log10 2 + 0x1.8p52` on floats. -/
def floatShifted (x : Float) : Float :=
  Float.ofBits 0x407A934F0979A371 * x + Float.ofBits 0x4338000000000000

/-- `k` on floats. -/
def floatInteger (x : Float) : Float := floatShifted x - Float.ofBits 0x4338000000000000

/-- The residual on floats. -/
def floatResidual (x : Float) : Float :=
  Float.ofBits 0x3D10C0219DC1DA99 * floatInteger x +
    (Float.ofBits 0xBF63441350A00000 * floatInteger x + x)

/-- `exp10Core`'s table index. -/
def index (ki : UInt64) : UInt64 := (ki &&& 127) * 2

/-- The tail selected by the key. -/
def tailFloat (x : Float) : Float :=
  Float.ofBits Exp.expTable[(index (floatShifted x).toBits).toNat]!

/-- The polynomial evaluation on floats, as `exp10Core` writes it. -/
def floatEvaluation (r t : Float) : Float :=
  let C0 := Float.ofBits 0x40026BB1BBB55516
  let C1 := Float.ofBits 0x40053524C73CE9FE
  let C2 := Float.ofBits 0x4000470591CE4B26
  let C3 := Float.ofBits 0x3FF2BD76577FE684
  let C4 := Float.ofBits 0x3FE1446EECCD0EFB
  let r2 := r * r
  let p := C0 + r * C1
  let y := C2 + r * C3
  let y := y + r2 * C4
  let y := p + r2 * y
  t + y * r

/-- The polynomial evaluation of `exp10Core`. -/
def tmpFloat (x : Float) : Float := floatEvaluation (floatResidual x) (tailFloat x)

/-- The scale bits of `exp10Core`. -/
def scaleBits (ki : UInt64) : UInt64 :=
  Exp.expTable[(index ki + 1).toNat]! + (ki <<< (45 : UInt64))

theorem core_eq (x : Float) (special : Bool) :
    Exp2.exp10Core Exp.expTable x special =
      if special then
        Exp2.exp2SpecialCase (tmpFloat x) (scaleBits (floatShifted x).toBits)
          (floatShifted x).toBits
      else Float.ofBits (scaleBits (floatShifted x).toBits) * tmpFloat x +
        Float.ofBits (scaleBits (floatShifted x).toBits) := by
  cases special <;> rfl

theorem index_eq (ki : UInt64) : index ki = ExpScaleBits.index ki := by
  apply UInt64.toNat_inj.mp
  simp only [index, ExpScaleBits.index, UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_mod,
    UInt64.reduceToNat]
  rw [show (127 : Nat) = 2 ^ 7 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  ring_nf

theorem scale_eq (ki : UInt64) : scaleBits ki = ExpScaleBits.scaleBits ki := by
  simp only [scaleBits, ExpScaleBits.scaleBits, index_eq]

theorem evaluation_bits (r t : Float) :
    (floatEvaluation r t).toBits = Exp10Evaluation.evaluation r.toBits t.toBits := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -⟩ := coefficient_finite
  simp only [floatEvaluation, Exp10Evaluation.evaluation, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, e1, e2, e3, e4, e5] at h1 h2 h3 h4 h5 ⊢
  simp only [not_nan_of_finite h1, not_nan_of_finite h2, not_nan_of_finite h3,
    not_nan_of_finite h4, not_nan_of_finite h5, Bool.false_eq_true, ite_false]

theorem shifted_bits (x : Float) : (floatShifted x).toBits = key x.toBits := by
  have hm := ExpIntegerSelection.magic_values.1
  have hi := coefficient_finite.2.2.2.2.2.2.2
  simp only [invWord] at hi
  simp only [floatShifted, key, ExpIntegerSelection.shifted, product, invWord,
    F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits, not_nan_of_finite hm,
    not_nan_of_finite hi, Bool.false_eq_true, ite_false]

theorem residual_bits (x : Float) : (floatResidual x).toBits = Exp10Reduction.residual x.toBits := by
  have hm := ExpIntegerSelection.magic_values.1
  obtain ⟨-, -, -, -, -, hhi, hlo, -⟩ := coefficient_finite
  simp only [hiWord, loWord] at hhi hlo
  simp only [floatResidual, floatInteger, Exp10Reduction.residual, Exp10Reduction.highResidual,
    Exp10Reduction.integer, ExpIntegerSelection.selected, hiWord, loWord, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_sub, shifted_bits, key, F64Bits.toBits_ofBits, not_nan_of_finite hm,
    not_nan_of_finite hhi, not_nan_of_finite hlo, Bool.false_eq_true, ite_false]

/-- Finite addition is commutative. -/
theorem add_comm_finite (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.add b a := by
  simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
    not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false,
    Bool.false_eq_true, ite_false, Int.add_comm, Bool.and_comm]

/-- The state of `exp10Core` for `|x| ≤ 400`. -/
theorem core_state (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| ≤ 400) :
    ∃ (k q : Int) (j : Fin 128),
      k = 128 * q + j.val ∧ |value x.toBits - (k : ℝ) * ratio| ≤ 1 / 850 ∧
      |(k : ℝ) - value x.toBits / ratio| ≤ 1 / 2 + 1 / 2 ^ 31 ∧ k.natAbs ≤ 2 ^ 18 ∧
      (((floatShifted x).toBits).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      (((floatShifted x).toBits) % 128).toNat = j.val ∧
      Finite (tmpFloat x).toBits ∧ |value (tmpFloat x).toBits| ≤ 1 / 64 ∧
      |value (tmpFloat x).toBits - (value (ExpTableBounds.tailBits j.val) +
        Real.exp ((value x.toBits - (k : ℝ) * ratio) * Real.log 10) - 1)| ≤ 1 / 2 ^ 56 := by
  obtain ⟨k, hif, hkv, hkn, hki, hideal, hdiff, hrf, herr, hrb⟩ := reduction_state x.toBits hxf hx
  obtain ⟨hm1, -, -⟩ := checked_margins
  have hm1R := Exp2Approximation.cast_le hm1
  push_cast at hm1R
  have hjk := ExpShiftedBits.euclidean_index k
  let j : Fin 128 := ⟨(k % 128).toNat, hjk.1⟩
  let q := k / 128
  have hk : k = 128 * q + j.val := hjk.2
  rw [← shifted_bits] at hki
  have hj : (((floatShifted x).toBits) % 128).toNat = j.val :=
    ExpShiftedBits.table_remainder _ k hki
  have hidx := (ExpScaleBits.index_values _ j hj).1
  rw [← index_eq] at hidx
  have htf := (ExpTableBounds.entry_bounds j).2.1
  have htail : (tailFloat x).toBits = ExpTableBounds.tailBits j.val := by
    simp only [tailFloat, F64Bits.toBits_ofBits, hidx]
    simp only [ExpTableBounds.tailBits] at htf ⊢
    simp only [not_nan_of_finite htf, Bool.false_eq_true, ite_false]
  have htb := (ExpTableBounds.entry_bounds j).2.2.2.2
  have hev := Exp10Evaluation.evaluation_error _ _ hrf htf hrb htb
  have hexp := Exp10Evaluation.evaluation_exp_error _ _ hrf htf hrb htb
  have htmp : (tmpFloat x).toBits =
      Exp10Evaluation.evaluation (Exp10Reduction.residual x.toBits) (ExpTableBounds.tailBits j.val) := by
    rw [tmpFloat, evaluation_bits, residual_bits, htail]
  -- the difference of `ρ` at the computed and the ideal residuals
  obtain ⟨hl, hh⟩ := log_ten_enclosure
  have hb := checked_reduction
  have hl' : (23 / 10 : ℝ) ≤ Real.log 10 := le_trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.1
    push_cast at this
    exact this) hl
  have hh' : Real.log 10 ≤ 233 / 100 := hh.trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.2.1
    push_cast at this
    exact this)
  have hiq : |value x.toBits - (k : ℝ) * ratio| ≤ 1 / 850 := by linarith [hideal]
  set a := value (Exp10Reduction.residual x.toBits) * Real.log 10
  set b := (value x.toBits - (k : ℝ) * ratio) * Real.log 10
  have hab : |a - b| ≤ 233 / 100 * (1 / 2 ^ 61) := by
    simp only [a, b]
    rw [← sub_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 10), mul_comm]
    exact mul_le_mul hh' herr (abs_nonneg _) (by norm_num)
  have hbb : |b| ≤ 1 / 364 := by
    simp only [b]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 10)]
    calc
      _ ≤ 1 / 850 * (233 / 100) := mul_le_mul hiq hh' (by linarith) (by norm_num)
      _ ≤ 1 / 364 := by norm_num
  have heb : Real.exp b ≤ 1 + 2 / 364 := by
    have := Real.abs_exp_sub_one_le (x := b) (hbb.trans (by norm_num))
    have := (abs_le.mp this).2
    linarith
  have hρ : |Real.exp a - Real.exp b| ≤ 1 / 2 ^ 58 := by
    have hd := Real.abs_exp_sub_one_le (x := a - b) (hab.trans (by norm_num))
    have hid : Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
      rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one]
    rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (1 + 2 / 364) * (2 * |a - b|) := mul_le_mul heb hd (abs_nonneg _) (by norm_num)
      _ ≤ (1 + 2 / 364) * (2 * (233 / 100 * (1 / 2 ^ 61))) := by gcongr
      _ ≤ 1 / 2 ^ 58 := by norm_num
  refine ⟨k, q, j, hk, hiq, ?_, hkn, hki, hj, ?_, ?_, ?_⟩
  · exact hdiff
  · rw [htmp]
    exact hev.1
  · rw [htmp]
    exact hev.2.1
  · rw [htmp]
    calc
      _ ≤ |value (Exp10Evaluation.evaluation (Exp10Reduction.residual x.toBits) (ExpTableBounds.tailBits j.val)) -
            (value (ExpTableBounds.tailBits j.val) + Real.exp a - 1)| +
          |Real.exp a - Real.exp b| := by
        have := abs_sub_le
          (value (Exp10Evaluation.evaluation (Exp10Reduction.residual x.toBits) (ExpTableBounds.tailBits j.val)))
          (value (ExpTableBounds.tailBits j.val) + Real.exp a - 1)
          (value (ExpTableBounds.tailBits j.val) + Real.exp b - 1)
        rw [show value (ExpTableBounds.tailBits j.val) + Real.exp a - 1 -
          (value (ExpTableBounds.tailBits j.val) + Real.exp b - 1) =
          Real.exp a - Real.exp b by ring] at this
        exact this
      _ ≤ 3 / 2 ^ 58 + 1 / 2 ^ 58 := add_le_add hexp hρ
      _ = 1 / 2 ^ 56 := by norm_num

#print axioms core_eq
#print axioms index_eq
#print axioms scale_eq
#print axioms evaluation_bits
#print axioms shifted_bits
#print axioms residual_bits
#print axioms add_comm_finite
#print axioms core_state

end Verified.Examples.Exp10Core
