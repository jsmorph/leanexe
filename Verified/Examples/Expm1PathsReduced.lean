import Verified.Examples.Expm1ReduceK
import Verified.Examples.Expm1FormsMid

/-!
The reduced paths of fdlibm's `expm1` on words, each within one step of `exp x - 1`: the
reductions of `Expm1ReduceOne` and `Expm1ReduceK` supply `y` and `c` with `y + c` near
`r = x - k log 2`, and the forms give one step against `2 ^ k exp r - 1 = exp x - 1`.
-/

namespace Verified.Examples.Expm1PathsReduced
open CodeLib.IEEE64 LeanExe.ProofKit Expm1ReduceConst Expm1ReduceOne Expm1ReduceK

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

/-- The overflow threshold of the code, `709.782712893384`. -/
def overflowWord : UInt64 := 0x40862E42FEFA39EF

theorem exp_two_pow (k : Nat) : Real.exp ((k : ℤ) * Real.log 2) = 2 ^ k := by
  push_cast
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem exp_shift_pos (X : ℝ) (k : Nat) :
    (2 : ℝ) ^ k * Real.exp (X - (k : ℤ) * Real.log 2) = Real.exp X := by
  rw [Real.exp_sub, exp_two_pow]
  field_simp

theorem exp_shift_neg (X : ℝ) (k : Nat) :
    Real.exp (X + (k : ℤ) * Real.log 2) / 2 ^ k = Real.exp X := by
  rw [Real.exp_add, exp_two_pow]
  field_simp

/-- At or below the overflow threshold, `x - 1024 log 2 ≤ -2 · 10 ^ -14`. -/
theorem overflow_gap : value overflowWord + 2 / 10 ^ 14 ≤ 1024 * Real.log 2 := by
  have h : PolyBound.ratOfWord overflowWord + 2 / 10 ^ 14 + 1024 / 2 ^ 92 ≤
      1024 * ExpReductionBounds.splitLogTwo := by
    unfold overflowWord
    decide +kernel
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast [PolyBound.ratOfWord_cast] at h'
  have hd := abs_le.mp log_two_near
  linarith [hd.1]

theorem overflow_value : value overflowWord ≤ 7097827128933840 / 10 ^ 13 := by
  rw [← PolyBound.ratOfWord_cast]
  have h : PolyBound.ratOfWord overflowWord ≤ 7097827128933840 / 10 ^ 13 := by
    unfold overflowWord
    decide +kernel
  exact ((Rat.cast_le (K := ℝ)).mpr h).trans_eq (by norm_num)

theorem exp_top (r : ℝ) (hr : r ≤ -2 / 10 ^ 14) : Real.exp r ≤ 1 - 1 / 2 ^ 46 := by
  have h1 := Real.add_one_le_exp (-r)
  have h2 : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos r
  have h3 : Real.exp r * (-r + 1) ≤ Real.exp r * Real.exp (-r) :=
    mul_le_mul_of_nonneg_left h1 hpos.le
  rw [h2] at h3
  by_contra h
  rw [not_le] at h
  have h4 : (1 - 1 / 2 ^ 46) * (-r + 1) < Real.exp r * (-r + 1) :=
    mul_lt_mul_of_pos_right h (by linarith)
  nlinarith

theorem word_one (m : UInt64) (h : m.toNat = 1) : m = 1 :=
  UInt64.toNat_inj.mp (by rw [h]; rfl)

/-- `k = 1`: `x` in `[0.34657359, 1.0397206)`. -/
theorem path_one_pos (x : UInt64) (hxf : Finite x) (hlo : 34657359 / 100000000 ≤ value x)
    (hhi : value x < 10397206 / 10000000) :
    let hi := Wasm.IEEE64.sub x ln2Hi
    let y := Wasm.IEEE64.sub hi ln2Lo
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1)
      (Expm1Words.kernel y (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) ln2Lo) false 1) := by
  intro hi y
  obtain ⟨hyf, hcf, hy, hc, hr⟩ := reduce_one_pos x hxf hlo hhi
  have he : 2 * Real.exp (value x - Real.log 2) - 1 = Real.exp (value x) - 1 := by
    have := exp_shift_pos (value x) 1
    push_cast at this
    rw [pow_one, one_mul] at this
    rw [this]
  rw [← he]
  by_cases hq : value y < -1 / 4
  · exact Expm1FormsOne.form_one_low y _ hyf hcf hy hc _ hr hq
  · exact Expm1FormsOne.form_one_high y _ hyf hcf hy hc _ hr hq

/-- `k = -1`: `x` in `(-1.0397206, -0.34657359]`. -/
theorem path_one_neg (x : UInt64) (hxf : Finite x) (hlo : -(10397206 / 10000000) < value x)
    (hhi : value x ≤ -(34657359 / 100000000)) :
    let hi := Wasm.IEEE64.add x ln2Hi
    let lo := Wasm.IEEE64.negate ln2Lo
    let y := Wasm.IEEE64.sub hi lo
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1)
      (Expm1Words.kernel y (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) lo) true 1) := by
  intro hi lo y
  obtain ⟨hyf, hcf, hy, hc, hr⟩ := reduce_one_neg x hxf hlo hhi
  have he : Real.exp (value x + Real.log 2) / 2 - 1 = Real.exp (value x) - 1 := by
    have := exp_shift_neg (value x) 1
    push_cast at this
    rw [pow_one, one_mul] at this
    rw [this]
  rw [← he]
  exact Expm1FormsOne.form_neg_one y _ hyf hcf hy hc _ hr

/-- `k ≥ 1` from the quotient: `x` in `[1.0397205, overflowWord]`. -/
theorem path_k_pos (x : UInt64) (hxf : Finite x) (hlo : 10397205 / 10 ^ 7 ≤ value x)
    (hhi : value x ≤ value overflowWord) :
    let m := Wasm.IEEE64.truncSatI64U (Wasm.IEEE64.add (Wasm.IEEE64.mul invln2 x) Expm1Words.half)
    let t := Wasm.IEEE64.convertI64U m
    let hi := Wasm.IEEE64.sub x (Wasm.IEEE64.mul t ln2Hi)
    let lo := Wasm.IEEE64.mul t ln2Lo
    let y := Wasm.IEEE64.sub hi lo
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1)
      (Expm1Words.kernel y (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) lo) false m) := by
  intro m t hi lo y
  obtain ⟨hm1, hm2, hyf, hcf, hy, hc, hr⟩ :=
    reduce_k_pos x hxf hlo (hhi.trans overflow_value)
  have hm1 : 1 ≤ m.toNat := hm1
  have hm2 : m.toNat ≤ 1024 := hm2
  have hr : |value y + value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) lo) -
      (value x - (m.toNat : ℤ) * Real.log 2)| ≤ 1 / 2 ^ 70 := hr
  have he := exp_shift_pos (value x) m.toNat
  rw [← he]
  rcases Nat.lt_or_ge m.toNat 2 with h1 | h2
  · have hm : m.toNat = 1 := by omega
    have hm' := word_one m hm
    rw [hm, pow_one]
    rw [hm] at hr
    rw [hm']
    by_cases hq : value y < -1 / 4
    · exact Expm1FormsOne.form_one_low y _ hyf hcf hy hc _ hr hq
    · exact Expm1FormsOne.form_one_high y _ hyf hcf hy hc _ hr hq
  rcases Nat.lt_or_ge m.toNat 20 with h20 | h20
  · exact Expm1FormsMid.form_mid_low y _ m hyf hcf hy hc _ hr h2 h20
  rcases Nat.lt_or_ge m.toNat 57 with h57 | h57
  · exact Expm1FormsMid.form_mid_high y _ m hyf hcf hy hc _ hr h20 (by omega)
  rcases Nat.lt_or_ge m.toNat 1024 with h1024 | h1024
  · exact Expm1FormsTwo.form_large y _ m hyf hcf hy hc _ hr h57 (by omega)
  have hm : m.toNat = 1024 := by omega
  rw [hm]
  rw [hm] at hr
  refine Expm1FormsTwo.form_top y _ m hyf hcf hy hc _ hr hm (exp_top _ ?_)
  have := overflow_gap
  push_cast
  linarith

/-- `k ≤ -1` from the quotient: `x` in `[-38.817, -1.0397205]`. -/
theorem path_k_neg (x : UInt64) (hxf : Finite x) (hlo : -38817 / 1000 ≤ value x)
    (hhi : value x ≤ -10397205 / 10 ^ 7) :
    let m := Wasm.IEEE64.truncSatI64U
      (Wasm.IEEE64.negate (Wasm.IEEE64.sub (Wasm.IEEE64.mul invln2 x) Expm1Words.half))
    let t := Wasm.IEEE64.negate (Wasm.IEEE64.convertI64U m)
    let hi := Wasm.IEEE64.sub x (Wasm.IEEE64.mul t ln2Hi)
    let lo := Wasm.IEEE64.mul t ln2Lo
    let y := Wasm.IEEE64.sub hi lo
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1)
      (Expm1Words.kernel y (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) lo) true m) := by
  intro m t hi lo y
  obtain ⟨hm1, hm2, hyf, hcf, hy, hc, hr⟩ := reduce_k_neg x hxf hlo hhi
  have hm1 : 1 ≤ m.toNat := hm1
  have hm2 : m.toNat ≤ 56 := hm2
  have hr : |value y + value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) lo) -
      (value x + (m.toNat : ℤ) * Real.log 2)| ≤ 1 / 2 ^ 70 := hr
  have he := exp_shift_neg (value x) m.toNat
  rw [← he]
  rcases Nat.lt_or_ge m.toNat 2 with h1 | h2
  · have hm : m.toNat = 1 := by omega
    have hm' := word_one m hm
    rw [hm, pow_one]
    rw [hm] at hr
    rw [hm']
    exact Expm1FormsOne.form_neg_one y _ hyf hcf hy hc _ hr
  exact Expm1FormsTwo.form_neg y _ m hyf hcf hy hc _ hr h2 hm2

#print axioms path_one_pos
#print axioms path_one_neg
#print axioms path_k_pos
#print axioms path_k_neg

end Verified.Examples.Expm1PathsReduced
