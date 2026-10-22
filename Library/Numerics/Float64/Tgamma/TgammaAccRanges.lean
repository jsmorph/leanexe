import Library.Numerics.Float64.Tgamma.TgammaAccPoly3
import Library.Numerics.Float64.Tgamma.TgammaApprox

/-!
`poly3` on the nine ranges of `Tgamma.accurate` above `1/4`.  The kernel checks the coefficients
of every range in `TgammaApprox.accRanges`: each double coefficient is a multiple of `2 ^ -17`
with a numerator below `2 ^ 19` and a magnitude at most 4, each double-double coefficient has a
high part at most `2 ^ -16` and a low part at most `2 ^ -70`, and the double-double coefficients
sum to at most `2 ^ -13` in magnitude (`coef_ok`, `dd_ok`, `dd_sum`).  `TgammaAccPoly3.poly3_spec` then puts
`poly3` within `2 ^ -63` of `TgammaApprox.accPoly` for `|d| ≤ 1` (`poly3_range`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccRanges
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaAccPoly3 TgammaApprox

set_option exponentiation.threshold 4096

/-- A double coefficient of the loop of `poly3`. -/
def coefOk (w : UInt64) : Bool :=
  Wasm.IEEE64.isFinite w && (PolyBound.ratOfWord w * 2 ^ 17).den == 1 &&
    decide ((PolyBound.ratOfWord w * 2 ^ 17).num.natAbs < 2 ^ 19) &&
    decide (PolyBound.qabs (PolyBound.ratOfWord w) ≤ 4)

/-- A double-double coefficient of `poly3`. -/
def ddOk (hi lo : UInt64) : Bool :=
  Wasm.IEEE64.isFinite hi && Wasm.IEEE64.isFinite lo &&
    decide (PolyBound.qabs (PolyBound.ratOfWord hi) ≤ 1 / 2 ^ 16) &&
    decide (PolyBound.qabs (PolyBound.ratOfWord lo) ≤ 1 / 2 ^ 70)

theorem sizes_ok : ∀ r ∈ accRanges, 1 ≤ r.2.1 ∧ r.2.1 ≤ 14 ∧ r.1 + r.2.1 < 2 ^ 63 ∧
    1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ 34 ∧ r.2.2.1 + 2 * r.2.2.2.1 < 2 ^ 63 := by decide +kernel

theorem coef_ok : ∀ r ∈ accRanges, ∀ k < r.2.1, coefOk accurateTable[r.1 + k]! = true := by
  decide +kernel

theorem dd_ok : ∀ r ∈ accRanges, ∀ k < r.2.2.2.1,
    ddOk accurateTable[r.2.2.1 + 2 * k]! accurateTable[r.2.2.1 + 2 * k + 1]! = true := by
  decide +kernel

theorem dd_sum : ∀ r ∈ accRanges, (∑ k ∈ Finset.range r.2.2.2.1,
    PolyBound.qabs (PolyBound.ratOfWord accurateTable[r.2.2.1 + 2 * k]! +
      PolyBound.ratOfWord accurateTable[r.2.2.1 + 2 * k + 1]!)) ≤ 1 / 2 ^ 13 := by
  decide +kernel

theorem coeffs_of (oh n : ℕ) (h : ∀ k < n, coefOk accurateTable[oh + k]! = true) :
    Coeffs accurateTable oh n := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := h k hk
    simp only [coefOk, Bool.and_eq_true] at this
    exact this.1.1.1
  · have := h k hk
    simp only [coefOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨⟨-, hden⟩, hnum⟩, -⟩ := this
    refine ⟨(PolyBound.ratOfWord accurateTable[oh + k]! * 2 ^ 17).num, ?_, hnum⟩
    have hq : ((PolyBound.ratOfWord accurateTable[oh + k]! * 2 ^ 17).num : ℚ) =
        PolyBound.ratOfWord accurateTable[oh + k]! * 2 ^ 17 := by
      exact (Rat.den_eq_one_iff _).mp hden
    have hr : ((PolyBound.ratOfWord accurateTable[oh + k]! : ℚ) : ℝ) =
        (((PolyBound.ratOfWord accurateTable[oh + k]! * 2 ^ 17).num : ℚ) : ℝ) / 2 ^ 17 := by
      rw [hq]; push_cast; field_simp
    rw [hr]
    norm_cast
  · have := h k hk
    simp only [coefOk, Bool.and_eq_true, decide_eq_true_eq] at this
    rw [← TgammaExpr.qabs_cast]
    exact_mod_cast this.2

theorem ddCoeffs_of (ol N : ℕ) (hol : ol < 2 ^ 63)
    (h : ∀ k < N, ddOk accurateTable[ol + 2 * k]! accurateTable[ol + 2 * k + 1]! = true)
    (hs : (∑ k ∈ Finset.range N, PolyBound.qabs (PolyBound.ratOfWord accurateTable[ol + 2 * k]! +
      PolyBound.ratOfWord accurateTable[ol + 2 * k + 1]!)) ≤ 1 / 2 ^ 13) :
    DDCoeffs accurateTable (UInt64.ofNat ol) N := by
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hol' : (UInt64.ofNat ol).toNat = ol := UInt64.toNat_ofNat_of_lt' (by omega)
  have hk : ∀ k < N, Wasm.IEEE64.isFinite accurateTable[ol + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite accurateTable[ol + 2 * k + 1]! = true ∧
      PolyBound.qabs (PolyBound.ratOfWord accurateTable[ol + 2 * k]!) ≤ 1 / 2 ^ 16 ∧
      PolyBound.qabs (PolyBound.ratOfWord accurateTable[ol + 2 * k + 1]!) ≤ 1 / 2 ^ 70 := by
    intro k hk
    have := h k hk
    simp only [ddOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, fun k hk' => ?_, fun k hk' => ?_, ?_⟩
  · rw [hol']; exact TgammaWords.ofBits_finite _ (hk k hk').1
  · rw [hol']; exact TgammaWords.ofBits_finite _ (hk k hk').2.1
  · rw [hol', TgammaWords.ofBits_value _ (hk k hk').1]
    have := TgammaSmall.abs_rat_le _ _ (hk k hk').2.2.1
    push_cast at this
    exact this
  · rw [hol', TgammaWords.ofBits_value _ (hk k hk').2.1]
    have := TgammaSmall.abs_rat_le _ _ (hk k hk').2.2.2
    push_cast at this
    exact this
  · have hc : ∀ k ∈ Finset.range N, |TgammaPolyDDD.cDD accurateTable (UInt64.ofNat ol) k| =
        ((PolyBound.qabs (PolyBound.ratOfWord accurateTable[ol + 2 * k]! +
          PolyBound.ratOfWord accurateTable[ol + 2 * k + 1]!) : ℚ) : ℝ) := by
      intro k hk'
      rw [Finset.mem_range] at hk'
      rw [TgammaWords.cDD_rat _ _ k (by rw [hol']; exact (hk k hk').1)
        (by rw [hol']; exact (hk k hk').2.1), TgammaExpr.qabs_cast, hol']
    rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
    calc _ ≤ ((1 / 2 ^ 13 : ℚ) : ℝ) := Rat.cast_le.mpr hs
      _ = 1 / 2 ^ 13 := by norm_num

/-- **`poly3` on the ranges of the accurate path** within `2 ^ -63` of `accPoly`. -/
theorem poly3_range (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d : Float) (hdf : Finite d.toBits)
    (hd : |value d.toBits| ≤ 1) (oh imax ol jmax j eoff : ℕ)
    (hr : (oh, imax, ol, jmax, j, eoff) ∈ accRanges) :
    Finite (poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax) (UInt64.ofNat ol)
        (UInt64.ofNat jmax)).1.toBits ∧
      Finite (poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax) (UInt64.ofNat ol)
        (UInt64.ofNat jmax)).2.toBits ∧
      |value (poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax) (UInt64.ofNat ol)
          (UInt64.ofNat jmax)).1.toBits +
        value (poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax) (UInt64.ofNat ol)
          (UInt64.ofNat jmax)).2.toBits - accPoly oh imax ol jmax (value d.toBits)| ≤ 1 / 2 ^ 63 ∧
      |value (poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax) (UInt64.ofNat ol)
        (UInt64.ofNat jmax)).1.toBits| ≤ 120 ∧
      |value (poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax) (UInt64.ofNat ol)
        (UInt64.ofNat jmax)).2.toBits| ≤ 1 / 2 ^ 37 := by
  obtain ⟨h1, h14, hoh, hj1, hj34, hol⟩ := sizes_ok _ hr
  dsimp only at h1 h14 hoh hj1 hj34 hol
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hohn : (UInt64.ofNat oh).toNat = oh := UInt64.toNat_ofNat_of_lt' (by omega)
  have himn : (UInt64.ofNat imax).toNat = imax := UInt64.toNat_ofNat_of_lt' (by omega)
  have holn : (UInt64.ofNat ol).toNat = ol := UInt64.toNat_ofNat_of_lt' (by omega)
  have hjmn : (UInt64.ofNat jmax).toNat = jmax := UInt64.toNat_ofNat_of_lt' (by omega)
  have hC : Coeffs accurateTable (UInt64.ofNat oh).toNat (UInt64.ofNat imax).toNat := by
    rw [hohn, himn]; exact coeffs_of oh imax (coef_ok (oh, imax, ol, jmax, j, eoff) hr)
  have hD : DDCoeffs accurateTable (UInt64.ofNat ol) (UInt64.ofNat jmax).toNat := by
    rw [hjmn]
    exact ddCoeffs_of ol jmax (by omega) (dd_ok (oh, imax, ol, jmax, j, eoff) hr)
      (dd_sum (oh, imax, ol, jmax, j, eoff) hr)
  obtain ⟨hp1, hp2, hpe, hpb1, hpb2⟩ := poly3_spec hF accurateTable d (UInt64.ofNat oh)
    (UInt64.ofNat imax) (UInt64.ofNat ol) (UInt64.ofNat jmax) (by rw [himn]; omega)
    (by rw [himn]; omega) (by rw [hohn, himn]; omega) hC (by rw [hjmn]; omega) (by rw [hjmn]; omega)
    (by rw [holn, hjmn]; omega) hD hdf hd
  refine ⟨hp1, hp2, ?_, hpb1, hpb2⟩
  have hacc : accPoly oh imax ol jmax (value d.toBits) =
      (∑ i ∈ Finset.range (UInt64.ofNat imax).toNat,
        coef accurateTable (UInt64.ofNat oh) i * value d.toBits ^ i) +
      ∑ k ∈ Finset.range (UInt64.ofNat jmax).toNat,
        TgammaPolyDDD.cDD accurateTable (UInt64.ofNat ol) k * value d.toBits ^ k := by
    rw [accPoly, TgammaWords.eval_coeffs, TgammaWords.eval_ddCoeffs, himn, hjmn]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [coef, hohn, TgammaWords.ofBits_value _
        ((coeffs_of oh imax (coef_ok (oh, imax, ol, jmax, j, eoff) hr)).fin i hi)]
      simp [q]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hk' := dd_ok (oh, imax, ol, jmax, j, eoff) hr k hk
      simp only [ddOk, Bool.and_eq_true, decide_eq_true_eq] at hk'
      rw [TgammaWords.cDD_rat _ _ k (by rw [holn]; exact hk'.1.1.1) (by rw [holn]; exact hk'.1.1.2),
        holn]
      simp [q]
  rw [hacc]
  exact hpe

#print axioms coef_ok
#print axioms dd_sum
#print axioms poly3_range

end Library.Numerics.Float64.Tgamma.TgammaAccRanges
