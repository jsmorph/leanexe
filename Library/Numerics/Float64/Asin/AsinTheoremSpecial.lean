import Library.Numerics.Float64.Asin.AcosTheorem
import Library.Numerics.Float64.Log1p.Log1pTheoremSpecial

/-!
The exceptional inputs of `Asin.asin` and `Asin.acos` as words: `asin` keeps `±0`, `acos 1` is
`+0`, and NaN, the infinities, and every finite `x` with `|x| > 1` give the canonical NaN through
`(x - x)/(x - x)`.
-/

namespace Library.Numerics.Float64.Asin.AsinTheoremSpecial
open CodeLib.IEEE64 LeanExe.ProofKit AsinTheoremBranches AsinTheorem AcosTheoremBranches

set_option exponentiation.threshold 4096

theorem asin_out_eq (x : Float) (h1 : ixA x ≥ 0x3ff00000)
    (h2 : (((ixA x - 0x3ff00000) ||| lxA x) == 0) = false) : Asin.asin x = (x - x) / (x - x) := by
  unfold ixA lxA at *
  simp only [Asin.asin, h1, h2, ite_true, Bool.false_eq_true, ite_false]

/-- `(w - w)/(w - w)` is the canonical NaN for every word. -/
theorem self_quot_nan (w : UInt64) :
    Wasm.IEEE64.div (Wasm.IEEE64.sub w w) (Wasm.IEEE64.sub w w) = Wasm.IEEE64.canonicalNaN := by
  by_cases hf : Finite w
  · rw [Library.Numerics.Float64.Log1p.Log1pTheoremSpecial.sub_self_bits w hf]
    decide +kernel
  by_cases hn : Wasm.IEEE64.isNaN w = true
  · have hs : Wasm.IEEE64.sub w w = Wasm.IEEE64.canonicalNaN := by
      simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, hn, Bool.true_or, ite_true]
    rw [hs]
    decide +kernel
  have hw := w.toNat_lt
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, bne_iff_ne, ne_eq, not_not, Bool.and_eq_true, beq_iff_eq,
    not_and] at hf hn
  have hb : w = 0x7FF0000000000000 ∨ w = 0xFFF0000000000000 := by
    rcases Nat.lt_or_ge w.toNat (2 ^ 63) with h | h
    · left
      apply UInt64.toNat_inj.mp
      rw [show (0x7FF0000000000000 : UInt64).toNat = 9218868437227405312 from rfl]
      omega
    · right
      apply UInt64.toNat_inj.mp
      rw [show (0xFFF0000000000000 : UInt64).toNat = 18442240474082181120 from rfl]
      omega
  rcases hb with rfl | rfl <;> decide +kernel

/-- An input outside `[-1, 1]`, infinite, or NaN takes the first branch, and it is not `±1`. -/
theorem out_conditions (x : Float) (h : ¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1)) :
    ixA x ≥ 0x3ff00000 ∧ (((ixA x - 0x3ff00000) ||| lxA x) == 0) = false := by
  have hix : (ixA x).toNat = x.toBits.toNat % 2 ^ 63 / 2 ^ 32 := F64UpperWord.high_toNat x.toBits
  have hlx : (lxA x).toNat = x.toBits.toNat % 2 ^ 32 := by
    unfold lxA
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hN := x.toBits.toNat_lt
  have hnu : x.toBits.toNat % 2 ^ 63 ≠ 0x3FF0000000000000 := by
    intro he
    apply h
    have hb : x.toBits = 0x3FF0000000000000 ∨ x.toBits = 0xBFF0000000000000 := by
      rcases Nat.lt_or_ge x.toBits.toNat (2 ^ 63) with hs | hs
      · left
        apply UInt64.toNat_inj.mp
        rw [show (0x3FF0000000000000 : UInt64).toNat = 4607182418800017408 from rfl]
        omega
      · right
        apply UInt64.toNat_inj.mp
        rw [show (0xBFF0000000000000 : UInt64).toNat = 13830554455654793216 from rfl]
        omega
    rcases hb with hb | hb <;> rw [hb] <;>
      refine ⟨by unfold CodeLib.IEEE64.Finite; decide, le_of_eq ?_⟩
    · rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by
        decide +kernel]
      norm_num
    · rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0xBFF0000000000000 = -1 by
        decide +kernel]
      norm_num
  have hge : 0x3ff00000 * 2 ^ 32 ≤ x.toBits.toNat % 2 ^ 63 := by
    by_contra hc
    apply h
    have hfin : Finite x.toBits := by
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
        ne_eq]
      omega
    refine ⟨hfin, le_of_lt ((ix_one x).mp ?_)⟩
    rw [UInt64.lt_iff_toNat_lt, hix, show (0x3ff00000 : UInt64).toNat = 1072693248 from rfl]
    omega
  have h1 : ixA x ≥ 0x3ff00000 := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le, hix, show (0x3ff00000 : UInt64).toNat = 1072693248 from rfl]
    omega
  refine ⟨h1, ?_⟩
  cases hc : (((ixA x - 0x3ff00000) ||| lxA x) == 0)
  · rfl
  · exfalso
    apply hnu
    simp only [beq_iff_eq] at hc
    have h3 := congrArg UInt64.toNat hc
    rw [UInt64.toNat_or, show (0 : UInt64).toNat = 0 from rfl, Nat.or_eq_zero_iff,
      UInt64.toNat_sub_of_le _ _ h1, hix, hlx,
      show (0x3ff00000 : UInt64).toNat = 1072693248 from rfl] at h3
    omega

theorem asin_nan (x : Float) (h : ¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1)) :
    (Asin.asin x).toBits = Wasm.IEEE64.canonicalNaN := by
  obtain ⟨h1, h2⟩ := out_conditions x h
  rw [asin_out_eq x h1 h2, F64Bits.toBits_div, F64Bits.toBits_sub]
  exact self_quot_nan x.toBits

theorem acos_nan (x : Float) (h : ¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1)) :
    (Asin.acos x).toBits = Wasm.IEEE64.canonicalNaN := by
  obtain ⟨h1, h2⟩ := out_conditions x h
  rw [acos_out_eq x h1 h2, F64Bits.toBits_div, F64Bits.toBits_sub]
  exact self_quot_nan x.toBits

theorem asin_zero (x : Float) (h : x.toBits = 0) : (Asin.asin x).toBits = 0 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by rw [h]; exact F64Magnitude.value_zero
  rw [asin_tiny_eq x (by unfold ixA; rw [h]; decide) (by unfold ixA; rw [h]; decide)
    (by unfold ixA; rw [h]; decide) (Library.Numerics.Float64.Atan.AtanTheorem.huge_gt x hx (by rw [hv, abs_zero]; norm_num)), h]

theorem asin_neg_zero (x : Float) (h : x.toBits = 0x8000000000000000) :
    (Asin.asin x).toBits = 0x8000000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by
    rw [h, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x8000000000000000 = 0 by
      decide +kernel]
    norm_num
  rw [asin_tiny_eq x (by unfold ixA; rw [h]; decide) (by unfold ixA; rw [h]; decide)
    (by unfold ixA; rw [h]; decide) (Library.Numerics.Float64.Atan.AtanTheorem.huge_gt x hx (by rw [hv, abs_zero]; norm_num)), h]

theorem acos_one (x : Float) (h : x.toBits = 0x3FF0000000000000) : (Asin.acos x).toBits = 0 := by
  rw [acos_one_eq x (by unfold ixA; rw [h]; decide) (by unfold ixA lxA; rw [h]; decide),
    if_pos (by rw [h]; decide)]
  rfl

#print axioms self_quot_nan
#print axioms asin_nan
#print axioms acos_nan
#print axioms asin_zero
#print axioms asin_neg_zero
#print axioms acos_one

end Library.Numerics.Float64.Asin.AsinTheoremSpecial
