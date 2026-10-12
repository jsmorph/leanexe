import LeanExe.ProofKit.F64NearestDiv
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64NearestSteps
import LeanExe.ProofKit.F64Source
import LeanExe.ProofKit.PolyBound

/-!
Rounded division with a quotient from `2 ^ 1022` up, which `F64NearestDiv.div_nearest` leaves out.
`round_rational_any` is `F64NearestDiv.round_rational` without the upper bound on the quotient: the
grid point `R 2 ^ s` within half a unit, with `R ≤ 2 ^ 53`.  `div_top` packs it with
`F64PowerScale.roundScaledMagnitude_shifted`: either the result is positive infinity and the
quotient is at least `F64PositiveRounding.overflowThreshold`, or the result is a nearest finite
word and the quotient is at most that threshold.  `nearest_top` states that a nearest word of a
number between the midpoint below the largest finite double and the threshold is the largest finite
double.
-/

namespace Verified.Examples.BesselDivTop
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestDiv F64NearestNonnegative

set_option exponentiation.threshold 4096

/-- `F64NearestDiv.round_rational` for every quotient from `2 ^ 52`. -/
theorem round_rational_any (N D : Nat) (hD : 0 < D) (hl : 2 ^ 52 * D ≤ N) :
    ∃ R s : Nat, R ≤ 2 ^ 53 ∧
      Wasm.IEEE64.roundRationalMagnitude false N D =
        Wasm.IEEE64.roundScaledMagnitude false (R * 2 ^ s) ∧
      (2 : ℝ) ^ (52 + s) ≤ (N : ℝ) / D ∧ (N : ℝ) / D < 2 ^ (53 + s) ∧
      |(R : ℝ) * 2 ^ s - (N : ℝ) / D| ≤ 2 ^ s / 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  set I := N / D with hI
  have hI52 : 2 ^ 52 ≤ I := (Nat.le_div_iff_mul_le hD).2 hl
  have hI0 : I ≠ 0 := by positivity
  set L := Nat.log2 I with hL
  have hL52 : 52 ≤ L := (Nat.le_log2 hI0).2 hI52
  have hL1 : 2 ^ L ≤ I := Nat.log2_self_le hI0
  have hL3 : I < 2 ^ (L + 1) := Nat.lt_log2_self
  set s := L - 52 with hs
  have hsL : 52 + s = L := by omega
  have hx1 : (I : ℝ) ≤ (N : ℝ) / D := by
    rw [le_div_iff₀ hDR]; exact_mod_cast Nat.div_mul_le_self N D
  have hx2 : (N : ℝ) / D < I + 1 := by
    rw [div_lt_iff₀ hDR]
    have : N < (I + 1) * D := by
      have := Nat.lt_div_mul_add (a := N) hD
      rw [hI]; nlinarith
    exact_mod_cast this
  have hxlo : (2 : ℝ) ^ (52 + s) ≤ (N : ℝ) / D := by
    rw [hsL]
    have : ((2 ^ L : ℕ) : ℝ) ≤ I := by exact_mod_cast hL1
    push_cast at this
    linarith
  have hxhi : (N : ℝ) / D < 2 ^ (53 + s) := by
    rw [show 53 + s = L + 1 by omega]
    have : (I : ℝ) + 1 ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast hL3
    push_cast at this
    linarith
  set R := Wasm.IEEE32.roundQuotient N (D * 2 ^ s) with hR
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hRe : |(R : ℝ) * 2 ^ s - (N : ℝ) / D| ≤ 2 ^ s / 2 := by
    have h := roundQuotient_error N (D * 2 ^ s) (by positivity)
    have h' : (R : ℝ) * 2 ^ s - (N : ℝ) / D = ((R : ℝ) - (N : ℝ) / ((D * 2 ^ s : ℕ) : ℝ)) * 2 ^ s := by
      push_cast; field_simp
    rw [h', abs_mul, abs_of_pos hP]
    calc |(R : ℝ) - (N : ℝ) / ((D * 2 ^ s : ℕ) : ℝ)| * 2 ^ s ≤ 1 / 2 * 2 ^ s :=
          mul_le_mul_of_nonneg_right h hP.le
      _ = 2 ^ s / 2 := by ring
  have hR53 : R ≤ 2 ^ 53 := by
    have h1 : (R : ℝ) * 2 ^ s ≤ 2 ^ 53 * 2 ^ s + 2 ^ s / 2 := by
      have := (abs_le.mp hRe).2
      have h2 : (2 : ℝ) ^ (53 + s) = 2 ^ 53 * 2 ^ s := pow_add _ _ _
      linarith
    have h3 : (R : ℝ) < 2 ^ 53 + 1 := by
      have : (R : ℝ) * 2 ^ s < (2 ^ 53 + 1) * 2 ^ s := by nlinarith
      exact lt_of_mul_lt_mul_right this hP.le
    have : R < 2 ^ 53 + 1 := by exact_mod_cast h3
    omega
  refine ⟨R, s, hR53, ?_, hxlo, hxhi, hRe⟩
  have hN0 : (N == 0) = false := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hl
    simpa using this.ne'
  have hD0 : (D == 0) = false := by simpa using hD.ne'
  unfold Wasm.IEEE64.roundRationalMagnitude
  simp only [hN0, hD0, Bool.false_eq_true, ite_false]
  congr 1
  rw [← hI, ← hL, ← hs]
  by_cases h0 : s = 0
  · simp only [hR, h0, pow_zero, Nat.mul_one, ite_self]
  · have hb : (s == 0) = false := by simpa using h0
    simp only [hb, Bool.false_eq_true, ite_false, hR]

theorem threshold_eq : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl

/-- A finite result `encodeFinite false e f` of magnitude `R 2 ^ s` with `R 2 ^ s` within half a
unit of `x = N / D` in the binade of `x` is a nearest word of `x / 2 ^ 1074`. -/
theorem nearest_of_grid (w : UInt64) (e f : Nat) (hw : w = Wasm.IEEE64.encodeFinite false e f)
    (he : e < 0x7FF) (hf : f < 2 ^ 52) (R s : Nat)
    (hm : Wasm.IEEE64.scaledMagnitude w = R * 2 ^ s) (x : ℝ)
    (hxlo : (2 : ℝ) ^ (52 + s) ≤ x) (hxhi : x < 2 ^ (53 + s))
    (hRe : |(R : ℝ) * 2 ^ s - x| ≤ 2 ^ s / 2) : Nearest (x / 2 ^ 1074) w := by
  have hfin : Finite w := by rw [hw]; exact finite_encodeFinite false e f he hf
  have hsg : Wasm.IEEE64.sign w = false := by
    rw [hw]; exact F64Source.sign_encodeFinite false e f (by omega) hf
  have hlim := F64Magnitude.lt_limit_of_finite w hfin hsg
  refine ⟨hlim, fun v hv => ?_⟩
  have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
  rw [F64NearestSum.value_of_lt_limit w hlim, F64NearestSum.value_of_lt_limit v hv, hm,
    ← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos h74]
  apply div_le_div_of_nonneg_right _ h74.le
  push_cast
  exact grid_nearest _ s R hxlo hxhi hRe _ (fun g hg => F64NearestSum.magnitude_dvd v g hg)

/-- Division of positive finite words with a quotient of at least `2 ^ 1022`. -/
theorem div_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hsa : Wasm.IEEE64.sign a = false) (hsb : Wasm.IEEE64.sign b = false)
    (hq : (2 : ℝ) ^ 1022 ≤ value a / value b) :
    (Wasm.IEEE64.div a b = F64PositiveRounding.positiveInfinity ∧
        F64PositiveRounding.overflowThreshold ≤ value a / value b) ∨
      (Nearest (value a / value b) (Wasm.IEEE64.div a b) ∧
        value a / value b ≤ F64PositiveRounding.overflowThreshold) := by
  set Ma := Wasm.IEEE64.scaledMagnitude a
  set Mb := Wasm.IEEE64.scaledMagnitude b
  have hva : value a = (Ma : ℝ) / 2 ^ 1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hsa, Ma]
  have hvb : value b = (Mb : ℝ) / 2 ^ 1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hsb, Mb]
  have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hqe : value a / value b = (Ma : ℝ) / Mb := by
    rw [hva, hvb]; field_simp
  rw [hqe] at hq ⊢
  have hMb : 0 < Mb := by
    rcases Nat.eq_zero_or_pos Mb with h | h
    · rw [h, Nat.cast_zero, div_zero] at hq; linarith [show (0 : ℝ) < 2 ^ 1022 by positivity]
    · exact h
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMb
  set N := Ma * 2 ^ 1074 with hN
  have hxq : (N : ℝ) / Mb = (Ma : ℝ) / Mb * 2 ^ 1074 := by
    rw [hN]; push_cast; ring
  have hq' : (2 : ℝ) ^ 2096 ≤ (N : ℝ) / Mb := by
    rw [hxq]
    have : (2 : ℝ) ^ 2096 = 2 ^ 1022 * 2 ^ 1074 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right hq h74.le
  have hl : 2 ^ 52 * Mb ≤ N := by
    have h1 : (2 : ℝ) ^ 52 ≤ (N : ℝ) / Mb := le_trans (by norm_num) hq'
    rw [le_div_iff₀ hMbR] at h1
    exact_mod_cast h1
  obtain ⟨R, s, hR53, heq, hxlo, hxhi, hRe⟩ := round_rational_any N Mb hMb hl
  have hdiv : Wasm.IEEE64.div a b = Wasm.IEEE64.roundRationalMagnitude false N Mb := by
    rw [CodeLib.IEEE64.div_finite_rounder a b ha hb hMb.ne', hsa, hsb]
    rfl
  have hqx : (Ma : ℝ) / Mb = (N : ℝ) / Mb / 2 ^ 1074 := by rw [hxq]; field_simp
  rw [hdiv, heq, hqx]
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hs44 : 2044 ≤ s := by
    by_contra h
    have : (2 : ℝ) ^ (53 + s) ≤ 2 ^ 2096 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hR52 : 2 ^ 52 ≤ R := by
    have h1 := (abs_le.mp hRe).1
    have h2 : (2 : ℝ) ^ (52 + s) = 2 ^ 52 * 2 ^ s := pow_add _ _ _
    have h3 : ((2 : ℝ) ^ 52 - 1) * 2 ^ s < (R : ℝ) * 2 ^ s := by nlinarith
    have h4 : (2 : ℝ) ^ 52 - 1 < R := lt_of_mul_lt_mul_right h3 hP.le
    have : 2 ^ 52 - 1 < R := by
      have e : ((2 ^ 52 - 1 : ℕ) : ℝ) = (2 : ℝ) ^ 52 - 1 := by norm_num
      exact_mod_cast (e ▸ h4)
    omega
  have hth := threshold_eq
  -- `R 2 ^ s` and the quotient in units of `2 ^ 1074`
  have hlow : ((R : ℝ) - 1 / 2) * 2 ^ s ≤ (N : ℝ) / Mb := by
    have := (abs_le.mp hRe).2; nlinarith
  have hupp : (N : ℝ) / Mb ≤ ((R : ℝ) + 1 / 2) * 2 ^ s := by
    have := (abs_le.mp hRe).1; nlinarith
  rcases Nat.lt_or_ge R (2 ^ 53) with hR | hR
  · rw [F64PowerScale.roundScaledMagnitude_shifted false R s hR52 hR]
    by_cases hinf : 0x7FF ≤ s + 1
    · rw [ite_eq_left hinf]
      left
      refine ⟨by decide, ?_⟩
      rw [hth, le_div_iff₀ h74]
      have h1 : (2 : ℝ) ^ (52 + 2046) ≤ 2 ^ (52 + s) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 1074 ≤ 2 ^ (52 + 2046) := by norm_num
      linarith
    · rw [ite_eq_right hinf]
      right
      have hf : R - 2 ^ 52 < 2 ^ 52 := by omega
      refine ⟨nearest_of_grid _ (s + 1) (R - 2 ^ 52) rfl (by omega) hf R s ?_ _ hxlo hxhi hRe, ?_⟩
      · rw [scaledMagnitude_encodeFinite false (s + 1) (R - 2 ^ 52) (by omega) hf,
          ite_eq_right (by omega), show s + 1 - 1 = s by omega,
          show 2 ^ 52 + (R - 2 ^ 52) = R by omega]
      · rw [hth, div_le_iff₀ h74]
        have hR1 : (R : ℝ) + 1 ≤ 2 ^ 53 := by
          have : R + 1 ≤ 2 ^ 53 := hR
          exact_mod_cast this
        have h1 : (2 : ℝ) ^ s ≤ 2 ^ 2045 := pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : ((2 : ℝ) ^ 53 - 1 / 2) * 2 ^ 2045 = (2 ^ 1024 - 2 ^ 970) * 2 ^ 1074 := by
          norm_num
        have h3 : ((R : ℝ) + 1 / 2) * 2 ^ s ≤ ((2 : ℝ) ^ 53 - 1 / 2) * 2 ^ 2045 :=
          mul_le_mul (by linarith) h1 hP.le (by norm_num)
        linarith
  · have hR' : R = 2 ^ 53 := le_antisymm hR53 hR
    have hshift : R * 2 ^ s = 2 ^ 52 * 2 ^ (s + 1) := by rw [hR', pow_succ]; ring
    rw [hshift, F64PowerScale.roundScaledMagnitude_shifted false (2 ^ 52) (s + 1) le_rfl
      (by norm_num)]
    by_cases hinf : 0x7FF ≤ s + 1 + 1
    · rw [ite_eq_left hinf]
      left
      refine ⟨by decide, ?_⟩
      rw [hth, le_div_iff₀ h74]
      have h1 : (2 : ℝ) ^ 2045 ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (by omega)
      have hRr : (R : ℝ) = 2 ^ 53 := by rw [hR']; norm_num
      rw [hRr] at hlow
      have h2 : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 1074 = ((2 : ℝ) ^ 53 - 1 / 2) * 2 ^ 2045 := by
        norm_num
      have h3 : ((2 : ℝ) ^ 53 - 1 / 2) * 2 ^ 2045 ≤ ((2 : ℝ) ^ 53 - 1 / 2) * 2 ^ s :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      linarith
    · rw [ite_eq_right hinf]
      right
      have hs44' : s = 2044 := by omega
      refine ⟨nearest_of_grid _ (s + 1 + 1) (2 ^ 52 - 2 ^ 52) rfl (by omega) (by norm_num) R s ?_
        _ hxlo hxhi hRe, ?_⟩
      · rw [scaledMagnitude_encodeFinite false (s + 1 + 1) (2 ^ 52 - 2 ^ 52) (by omega)
          (by norm_num), ite_eq_right (by omega), hR', show s + 1 + 1 - 1 = s + 1 by omega,
          Nat.sub_self, Nat.add_zero, pow_succ, pow_succ]
        ring
      · rw [hth, div_le_iff₀ h74]
        have hRr : (R : ℝ) = 2 ^ 53 := by rw [hR']; norm_num
        rw [hRr, hs44'] at hupp
        have h2 : ((2 : ℝ) ^ 53 + 1 / 2) * 2 ^ 2044 ≤ (2 ^ 1024 - 2 ^ 970) * 2 ^ 1074 := by
          norm_num
        linarith

/-- The largest finite double. -/
def maxWord : UInt64 := 0x7FEFFFFFFFFFFFFF

theorem value_max : value maxWord = 2 ^ 1024 - 2 ^ 971 := by
  rw [maxWord, ← PolyBound.ratOfWord_cast]
  have : PolyBound.ratOfWord 0x7FEFFFFFFFFFFFFF = 2 ^ 1024 - 2 ^ 971 := by decide +kernel
  rw [this]; norm_num

theorem value_below_max : value (0x7FEFFFFFFFFFFFFE : UInt64) = 2 ^ 1024 - 2 ^ 972 := by
  rw [← PolyBound.ratOfWord_cast]
  have : PolyBound.ratOfWord 0x7FEFFFFFFFFFFFFE = 2 ^ 1024 - 2 ^ 972 := by decide +kernel
  rw [this]; norm_num

/-- A nearest word of `t` with `2 ^ 1024 - 3 · 2 ^ 970 < t ≤ overflowThreshold` is the largest
finite double. -/
theorem nearest_top (t : ℝ) (w : UInt64) (hw : Nearest t w) (h1 : 2 ^ 1024 - 3 * 2 ^ 970 < t)
    (h2 : t ≤ F64PositiveRounding.overflowThreshold) : w.toNat = 0x7FEFFFFFFFFFFFFF := by
  have hth := threshold_eq
  have hge := F64NearestSteps.nearest_ge t w 0x7FEFFFFFFFFFFFFE hw (by decide) (by
    rw [value_below_max]
    have : (2 : ℝ) ^ 1024 - 2 ^ 972 ≤ 2 ^ 1024 - 3 * 2 ^ 970 := by norm_num
    linarith)
  have hlt := hw.1
  have hl : limit = 0x7FF0000000000000 := rfl
  rw [hl] at hlt
  simp only [UInt64.reduceToNat] at hge
  rcases Nat.lt_or_ge w.toNat 0x7FEFFFFFFFFFFFFF with h | h
  · exfalso
    have hw2 : w = 0x7FEFFFFFFFFFFFFE := UInt64.toNat_inj.mp (by
      simp only [UInt64.reduceToNat]; omega)
    have hd := hw.2 maxWord (by decide)
    rw [hw2, value_below_max, value_max] at hd
    rw [hth] at h2
    have e : (2 : ℝ) ^ 971 = 2 * 2 ^ 970 := by norm_num
    have e2 : (2 : ℝ) ^ 972 = 4 * 2 ^ 970 := by norm_num
    have e3 : (2 : ℝ) ^ 1024 = 2 ^ 54 * 2 ^ 970 := by norm_num
    rw [e, e2, e3] at hd
    rw [e3] at h1 h2
    have hp : (0 : ℝ) < 2 ^ 970 := by positivity
    have hl1 : |2 ^ 54 * 2 ^ 970 - 4 * 2 ^ 970 - t| = t - (2 ^ 54 * 2 ^ 970 - 4 * 2 ^ 970) := by
      rw [abs_of_neg (by linarith)]; ring
    have hr : |2 ^ 54 * 2 ^ 970 - 2 * 2 ^ 970 - t| ≤ 2 ^ 970 := by
      rw [abs_le]; constructor <;> linarith
    rw [hl1] at hd
    linarith
  · omega

#print axioms round_rational_any
#print axioms nearest_of_grid
#print axioms div_top
#print axioms nearest_top

end Verified.Examples.BesselDivTop
