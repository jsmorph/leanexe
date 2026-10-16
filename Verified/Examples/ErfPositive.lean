import Verified.Examples.ErfSmall
import Verified.Examples.ErfMiddle
import Verified.Examples.ErfSub
import Verified.Examples.ErfTailErf
import Verified.Examples.ErfBits

/-!
One step for `Erf.erfWith Exp.expTable x` for every finite `x` with a clear sign bit.  The code's
path for each range of `x` (`ErfBits.sel_inf_free`) becomes a word expression through the
`F64Bits` lemmas, and the range's theorem gives the step: `ErfSub` below `2^-1015`, `ErfEnds` below
`2^-28` and from 6 on, `ErfSmall` below `0.84375`, `ErfMiddle` below 1.25, and `ErfTailErf` on the
tail, where `expWith_relative`, from `ExpTightFloat.exp_relative`, supplies the exponentials'
relative errors.
-/

namespace Verified.Examples.ErfPositive
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner RealErf ErfSmallBase ErfMiddleBase ErfTailSplit
  ErfTailEval ErfEnds ErfSub ErfBits

set_option exponentiation.threshold 4096

/-- `Exp.expWith Exp.expTable x` within `1.405 u exp x` for `|x| < 512`, the bound that the tail's
theorems take, from the bound `1.033 u exp x` of `ExpTightFloat.exp_relative`. -/
theorem expWith_relative (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 512) :
    Finite (Exp.expWith Exp.expTable x).toBits ∧
      |value (Exp.expWith Exp.expTable x).toBits - Real.exp (value x.toBits)| ≤
        (1405 / 1000) * unitRoundoff64 * Real.exp (value x.toBits) := by
  have hb := abs_lt.mp hx
  have h512 : (512 : ℝ) ≤ 7097827 / 10 ^ 4 := by norm_num
  obtain ⟨hf, he⟩ := ExpTightFloat.exp_relative x hxf (by linarith) (by linarith)
  have hE := Real.exp_pos (value x.toBits)
  have hu : (0 : ℝ) < unitRoundoff64 := by norm_num [unitRoundoff64]
  refine ⟨hf, he.trans ?_⟩
  nlinarith [mul_pos hu hE]

theorem abs_eq_self (b : UInt64) (hs : Wasm.IEEE64.sign b = false) : Wasm.IEEE64.abs b = b := by
  have hb := b.toNat_lt
  have hsz : UInt64.size = 18446744073709551616 := rfl
  have hb63 : b.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  apply UInt64.toNat_inj.mp
  rw [Wasm.IEEE64.abs, F64Magnitude.positive_encoding_toNat (Wasm.IEEE64.exponent b)
    (Wasm.IEEE64.fraction b) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  omega

theorem eight_bits : (8.0 : Float).toBits = 0x4020000000000000 := rfl
theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
theorem c0625_bits : (0.5625 : Float).toBits = 0x3FE2000000000000 := rfl

/-- A word with a clear sign bit and value 0 is positive zero. -/
theorem eq_zero_of_value (b : UInt64) (hs : Wasm.IEEE64.sign b = false) (h0 : value b = 0) :
    b = 0 := by
  have hb := b.toNat_lt
  have hb63 : b.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hm : Wasm.IEEE64.scaledMagnitude b = 0 := by
    have : (Wasm.IEEE64.scaledMagnitude b : ℝ) / 2 ^ 1074 = 0 := by
      simpa [value, Wasm.IEEE64.scaledValue, hs] using h0
    have h2 : (Wasm.IEEE64.scaledMagnitude b : ℝ) = 0 := by
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h (by positivity)
    exact_mod_cast h2
  have he : Wasm.IEEE64.exponent b = 0 := by
    by_contra h
    have : (Wasm.IEEE64.exponent b == 0) = false := beq_false_of_ne h
    simp only [Wasm.IEEE64.scaledMagnitude, this, Bool.false_eq_true, ↓reduceIte] at hm
    have : 0 < (2 ^ 52 + Wasm.IEEE64.fraction b) * 2 ^ (Wasm.IEEE64.exponent b - 1) := by positivity
    omega
  have hf : Wasm.IEEE64.fraction b = 0 := by
    simpa [Wasm.IEEE64.scaledMagnitude, he] using hm
  apply UInt64.toNat_inj.mp
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at he hf
  simp only [UInt64.toNat_zero]
  omega

theorem within_zero : F64SignedRounding.WithinSteps 1 0 0 := by
  have h0 : F64PositiveRounding.roundNearestEven 0 = 0 := F64SignedRounding.positive_reference_zero
  exact F64SignedRounding.within_of_nonneg 1 0 le_rfl 0 (by decide) (by rw [h0]; decide)
    (by rw [h0]; decide)

/-- The tail, with the words of the code. -/
theorem tail_pos (x : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = false)
    (hlo : 5 / 4 ≤ value x.toBits) (hhi : value x.toBits < 6) :
    F64SignedRounding.WithinSteps 1 (erf (value x.toBits))
      (1.0 - Erf.erfExp Exp.expTable x.abs
        (Erf.erfTail (1.0 / (x.abs * x.abs)) ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).1
        (Erf.erfTail (1.0 / (x.abs * x.abs))
          ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).2 / x.abs).toBits := by
  have hxa : x.abs.toBits = x.toBits := by rw [F64Bits.toBits_abs, abs_eq_self _ hs]
  obtain ⟨hzf, _, _, _, _, _, _, _, _⟩ := z_facts x.toBits hxf (by linarith) (by linarith)
  have hzn : Wasm.IEEE64.isNaN (zWord x.toBits) = false := not_nan_of_finite hzf
  have hon : Wasm.IEEE64.isNaN (0x3FF0000000000000 : UInt64) = false := by decide
  -- the words of the code
  have hz : (Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000)).toBits = zWord x.toBits := by
    rw [hxa, F64Bits.toBits_ofBits]
    simp only [zWord] at hzn ⊢
    simp [hzn]
  have hnz : (-Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000)).toBits =
      Wasm.IEEE64.negate (zWord x.toBits) := by
    rw [F64Bits.toBits_neg, hz, F64Sign.sub_negZero, hzn]
    rfl
  set a1 := -Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) *
    Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) - 0.5625 with ha1def
  have ha1 : a1.toBits = Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord x.toBits)) (zWord x.toBits))
      0x3FE2000000000000 := by
    rw [ha1def, F64Bits.toBits_sub, F64Bits.toBits_mul, hnz, hz, c0625_bits]
  have hs1 : (1.0 / (x.abs * x.abs)).toBits =
      Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul x.toBits x.toBits) := by
    rw [F64Bits.toBits_div, F64Bits.toBits_mul, hxa, one_bits]
  have hE1 : Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord x.toBits)) (zWord x.toBits))
        0x3FE2000000000000) →
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord x.toBits)) (zWord x.toBits))
        0x3FE2000000000000)| < 512 →
      Finite (Exp.expWith Exp.expTable a1).toBits ∧
        |value (Exp.expWith Exp.expTable a1).toBits - Real.exp (value (Wasm.IEEE64.sub
          (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord x.toBits)) (zWord x.toBits)) 0x3FE2000000000000))| ≤
        (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
          (Wasm.IEEE64.negate (zWord x.toBits)) (zWord x.toBits)) 0x3FE2000000000000)) := by
    intro hf hl
    rw [← ha1] at hf hl ⊢
    exact expWith_relative a1 hf hl
  have hdiv : ∀ (R S : Float), (1.0 - Erf.erfExp Exp.expTable x.abs R S / x.abs).toBits =
      Wasm.IEEE64.sub 0x3FF0000000000000 (Wasm.IEEE64.div (Wasm.IEEE64.mul
        (Exp.expWith Exp.expTable a1).toBits
        (Exp.expWith Exp.expTable
          ((Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) - x.abs) *
            (Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) + x.abs) + R / S)).toBits) x.toBits) := by
    intro R S
    simp only [Erf.erfExp, F64Bits.toBits_sub, F64Bits.toBits_div, F64Bits.toBits_mul, one_bits,
      hxa, ha1def]
  by_cases hn : value x.toBits < (ErfTailCoeffs.tailB2 : ℝ)
  · have hnear : ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E) := ((ix_conds x hxf).2.2.2.2.2.2).mpr
      (by rw [abs_of_nonneg (by linarith)]; exact hn)
    simp only [hnear, decide_true]
    rw [hdiv]
    obtain ⟨hR, hS⟩ := erfTail_bits (1.0 / (x.abs * x.abs)) true
    simp only [ite_true] at hR hS
    set a2 := (Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) - x.abs) *
      (Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) + x.abs) +
      (Erf.erfTail (1.0 / (x.abs * x.abs)) true).1 / (Erf.erfTail (1.0 / (x.abs * x.abs)) true).2
      with ha2def
    have ha2 : a2.toBits = Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord x.toBits) x.toBits) (Wasm.IEEE64.add (zWord x.toBits) x.toBits))
        (Wasm.IEEE64.div (hornerW raW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul x.toBits x.toBits)))
          (hornerW saW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul x.toBits x.toBits)))) := by
      rw [ha2def, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_sub, F64Bits.toBits_add,
        F64Bits.toBits_div, hR, hS, hs1, hz, hxa]
    exact ErfTailErf.tail_erf_a x.toBits hxf hlo hn.le _ _ hE1 (by
      intro hf hl
      rw [← ha2] at hf hl ⊢
      exact expWith_relative a2 hf hl)
  · have hnear : ¬ ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E) := fun h =>
      hn (by have := ((ix_conds x hxf).2.2.2.2.2.2).mp h; rwa [abs_of_nonneg (by linarith)] at this)
    simp only [hnear, decide_false]
    rw [hdiv]
    obtain ⟨hR, hS⟩ := erfTail_bits (1.0 / (x.abs * x.abs)) false
    simp only [Bool.false_eq_true, ite_false] at hR hS
    set a2 := (Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) - x.abs) *
      (Float.ofBits (x.abs.toBits &&& 0xFFFFFFFF00000000) + x.abs) +
      (Erf.erfTail (1.0 / (x.abs * x.abs)) false).1 / (Erf.erfTail (1.0 / (x.abs * x.abs)) false).2
      with ha2def
    have ha2 : a2.toBits = Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord x.toBits) x.toBits) (Wasm.IEEE64.add (zWord x.toBits) x.toBits))
        (Wasm.IEEE64.div (hornerW rbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul x.toBits x.toBits)))
          (hornerW sbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul x.toBits x.toBits)))) := by
      rw [ha2def, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_sub, F64Bits.toBits_add,
        F64Bits.toBits_div, hR, hS, hs1, hz, hxa]
    exact ErfTailErf.tail_erf_b x.toBits hxf (not_lt.mp hn) hhi.le _ _ hE1 (by
      intro hf hl
      rw [← ha2] at hf hl ⊢
      exact expWith_relative a2 hf hl)

/-- One step for `erf x` for every finite `x` with a clear sign bit. -/
theorem erf_pos (x : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = false) :
    F64SignedRounding.WithinSteps 1 (erf (value x.toBits)) (Erf.erfWith Exp.expTable x).toBits := by
  have hv0 : 0 ≤ value x.toBits := by
    simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ↓reduceIte]
    positivity
  obtain ⟨_, hsm, htiny, hsub, hmid, hsix, _⟩ := ix_conds x hxf
  have habs : |value x.toBits| = value x.toBits := abs_of_nonneg hv0
  rw [habs] at hsm htiny hsub hmid hsix
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = false := by rw [neg_flag]; exact hs
  have hxa : x.abs.toBits = x.toBits := by rw [F64Bits.toBits_abs, abs_eq_self _ hs]
  rw [sel_inf_free _ x hxf]
  simp only [hneg, Bool.false_eq_true, ↓reduceIte]
  have n8 : Wasm.IEEE64.isNaN 0x3FF06EBA8214DB69 = false := by decide
  have n1 : Wasm.IEEE64.isNaN 0x3FC06EBA8214DB69 = false := by decide
  have ne : Wasm.IEEE64.isNaN 0x3FEB0AC160000000 = false := by decide
  have nt : Wasm.IEEE64.isNaN 0x01A56E1FC2F8F359 = false := by decide
  by_cases h1 : value x.toBits < 27 / 32
  · rw [if_pos (hsm.mpr h1)]
    by_cases h2 : value x.toBits < 1 / 2 ^ 28
    · rw [if_pos (htiny.mpr h2)]
      by_cases h3 : value x.toBits < 1 / 2 ^ 1015
      · rw [if_pos (hsub.mpr h3)]
        rw [F64Bits.toBits_div, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_mul,
          F64Bits.toBits_ofBits, n8, eight_bits]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases eq_or_lt_of_le hv0 with h0 | h0
        · have hb0 := eq_zero_of_value x.toBits hs h0.symm
          rw [hb0, F64Magnitude.value_zero, erf_zero]
          have hw : Wasm.IEEE64.div (Wasm.IEEE64.add (Wasm.IEEE64.mul 0x4020000000000000 0)
              (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 0)) 0x4020000000000000 = 0 := by decide +kernel
          rw [hw]
          exact within_zero
        · by_cases h4 : value x.toBits < 1 / 2 ^ 1022
          · exact erf_subnormal x.toBits hxf h0 h4
          · exact erf_sub_normal x.toBits hxf (not_lt.mp h4) h3.le
      · rw [if_neg (fun h => h3 (hsub.mp h))]
        rw [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits, n1]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact erf_tiny x.toBits hxf (not_lt.mp h3) h2.le
    · rw [if_neg (fun h => h2 (htiny.mp h))]
      rw [F64Bits.toBits_add, F64Bits.toBits_mul, erfSmall_bits, F64Bits.toBits_mul]
      exact ErfSmall.small_erf x.toBits hxf (not_lt.mp h2) h1.le
  · rw [if_neg (fun h => h1 (hsm.mp h))]
    by_cases h2 : value x.toBits < 5 / 4
    · rw [if_pos (hmid.mpr h2)]
      obtain ⟨hP, hQ⟩ := erfMiddle_bits (x.abs - 1.0)
      rw [F64Bits.toBits_add, F64Bits.toBits_div, hP, hQ, F64Bits.toBits_sub, hxa, one_bits,
        F64Bits.toBits_ofBits, ne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ErfMiddle.middle_erf_all x.toBits hxf (not_lt.mp h1) h2.le
    · rw [if_neg (fun h => h2 (hmid.mp h))]
      by_cases h3 : 6 ≤ value x.toBits
      · rw [if_pos (hsix.mpr h3)]
        rw [F64Bits.toBits_sub, F64Bits.toBits_ofBits, nt, one_bits]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [one_sub_tiny]
        exact erf_large x.toBits h3
      · rw [if_neg (fun h => h3 (hsix.mp h))]
        exact tail_pos x hxf hs (not_lt.mp h2) (not_le.mp h3)

#print axioms expWith_relative
#print axioms abs_eq_self
#print axioms eq_zero_of_value
#print axioms tail_pos
#print axioms erf_pos

end Verified.Examples.ErfPositive
