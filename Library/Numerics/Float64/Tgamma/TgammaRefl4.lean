import Library.Numerics.Float64.Tgamma.TgammaBits
import Library.Numerics.Float64.Tgamma.TgammaExpLow

/-!
The real error analysis of the path of `tgammaWith` below `-3`, with the hypotheses that other
tracks prove: `SinpidSpec`, the specification of `asSinpid` from track `expm1`, and `SubnormalGap`,
the gap of `|Γ|` around `2 ^ -1022` from track `erf`.  With `K = sin (π d) Γ (1 - x)` and
`P = 2 ^ E`, the code's quotient `rh + rl` approximates `T = π P/K = |Γ x| P` within `11 · 2 ^ -60`
relative, and `rh` alone within `24 · 2 ^ -53` relative (`refl_real`), the margin that the choice of
the subnormal branch below `-170` needs against the gap of `32 · 2 ^ -53`.  `grid` and `sin_lower`
bound `sin (π d)` below by `2 ^ -50`, since a double below `-2` is a multiple of `2 ^ -51`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaRefl4
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaFloor

set_option exponentiation.threshold 4096

/-- The specification of `Tgamma.asSinpid` at the doubles `n / 2 ^ 53` of `(0, 1)`, the grid on
which `TgammaSinpid.asSinpid_spec` proves it and which holds the fractional part of every double
below `-2`. -/
def SinpidSpec : Prop :=
  ∀ (d : Float) (n : ℕ), 0 < n → n < 2 ^ 53 → Finite d.toBits → value d.toBits = n / 2 ^ 53 →
    Finite (asSinpid sinpidTable d).1.toBits ∧ Finite (asSinpid sinpidTable d).2.toBits ∧
    |value (asSinpid sinpidTable d).1.toBits + value (asSinpid sinpidTable d).2.toBits -
        Real.sin (Real.pi * value d.toBits)| ≤ Real.sin (Real.pi * value d.toBits) / 2 ^ 58 ∧
    |value (asSinpid sinpidTable d).2.toBits| ≤ |value (asSinpid sinpidTable d).1.toBits| / 2 ^ 50

/-- The gap of `|Γ|` around `2 ^ -1022` at the doubles of `(-184, -170)`, which track `erf` proves
as `GammaSubnormal.subnormal_gap`. -/
def SubnormalGap : Prop :=
  ∀ m : ℕ, 170 * 2 ^ 45 < m → m < 184 * 2 ^ 45 →
    |Real.Gamma (-(m : ℝ) / 2 ^ 45)| ≤ 2 ^ (-1022 : ℤ) * (1 - 1 / 2 ^ 48) ∨
      2 ^ (-1022 : ℤ) * (1 + 1 / 2 ^ 48) ≤ |Real.Gamma (-(m : ℝ) / 2 ^ 45)|

/-- A number `j / 2 ^ 51` of `(0, 1)` is `n / 2 ^ 53` for `n = 4 j`, with `0 < n < 2 ^ 53`. -/
theorem fract_grid (f : ℝ) (j : ℤ) (hj : f = j / 2 ^ 51) (h0 : 0 < f) (h1 : f < 1) :
    0 < (4 * j).toNat ∧ (4 * j).toNat < 2 ^ 53 ∧ f = ((4 * j).toNat : ℝ) / 2 ^ 53 := by
  have hj0 : (0 : ℝ) < j := by
    rw [hj] at h0
    exact (div_pos_iff_of_pos_right (by positivity)).mp h0
  have hj1 : (j : ℝ) < 2 ^ 51 := by
    rw [hj, div_lt_one (by positivity)] at h1
    exact h1
  have hj0' : (0 : ℤ) < j := by exact_mod_cast hj0
  have hj1' : j < 2251799813685248 := by
    have : (j : ℝ) < 2251799813685248 := by norm_num at hj1 ⊢; exact hj1
    exact_mod_cast this
  have hn : ((4 * j).toNat : ℤ) = 4 * j := Int.toNat_of_nonneg (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [show (2 : ℕ) ^ 53 = 9007199254740992 by norm_num]
    omega
  · have hc : ((4 * j).toNat : ℝ) = 4 * (j : ℝ) := by exact_mod_cast hn
    rw [hc, hj]
    ring

/-- A double of magnitude at least `2 ^ a` is a multiple of `2 ^ (a - 52)`. -/
theorem grid (w : UInt64) (a : ℕ) (ha : a ≤ 52) (h : (2 : ℝ) ^ a ≤ |value w|) :
    ∃ k : ℤ, value w = k / 2 ^ (52 - a) := by
  have he : 1023 + a ≤ Wasm.IEEE64.exponent w := by
    by_contra hc
    have := F64Magnitude.magnitude_lt w (1023 + a) (a : ℤ) (by omega) (by push_cast; ring)
      (by omega)
    rw [zpow_natCast] at this
    linarith
  obtain ⟨k, hk⟩ := F64Sterbenz.scaled_dvd w (1022 + a) (by omega)
  refine ⟨k, ?_⟩
  rw [value, hk]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity),
    show (2 : ℝ) ^ 1074 = 2 ^ 1022 * 2 ^ a * 2 ^ (52 - a) by
      rw [← pow_add, ← pow_add]; congr 1; omega]
  ring

/-- `sin (π d)` for a multiple `d` of `2 ^ -51` in `(0, 1)`. -/
theorem sin_lower (d : ℝ) (k : ℤ) (hd : d = k / 2 ^ 51) (h0 : 0 < d) (h1 : d < 1) :
    1 / 2 ^ 50 ≤ Real.sin (Real.pi * d) := by
  have hk1 : (1 : ℝ) ≤ k := by
    have : (0 : ℝ) < k := by
      rw [hd] at h0
      exact (div_pos_iff_of_pos_right (by positivity)).mp h0
    have : (0 : ℤ) < k := by exact_mod_cast this
    exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hk2 : (k : ℝ) ≤ 2 ^ 51 - 1 := by
    have : (k : ℝ) < 2 ^ 51 := by
      rw [hd, div_lt_one (by positivity)] at h1
      exact h1
    have : k < 2 ^ 51 := by exact_mod_cast this
    exact_mod_cast (show k ≤ 2 ^ 51 - 1 by omega)
  have hdlo : 1 / 2 ^ 51 ≤ d := by
    rw [hd]; exact div_le_div_of_nonneg_right hk1 (by positivity)
  have hdhi : d ≤ 1 - 1 / 2 ^ 51 := by
    rw [hd, div_le_iff₀ (by positivity)]
    linarith
  have hpi := Real.pi_pos
  rcases le_or_gt d (1 / 2) with hle | hgt
  · have h := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * d) (by nlinarith)
    have : 2 / Real.pi * (Real.pi * d) = 2 * d := by field_simp
    linarith
  · rw [← Real.sin_pi_sub]
    have h := Real.mul_le_sin (by nlinarith : 0 ≤ Real.pi - Real.pi * d) (by nlinarith)
    have : 2 / Real.pi * (Real.pi - Real.pi * d) = 2 * (1 - d) := by field_simp
    linarith

/-- `(h + l) 2 ^ E` against `Γ1` from the errors of `asLgammaAsym` and `asExpd`. -/
theorem exp_close (Γ1 Y Q : ℝ) (hΓ : 0 < Γ1) (hY : |Y - Real.log Γ1| ≤ 1 / 2 ^ 60)
    (hQ : |Q - Real.exp Y| ≤ Real.exp Y / 2 ^ 59) : |Q - Γ1| ≤ 5 * Γ1 / 2 ^ 60 := by
  have hEG : |Real.exp Y - Γ1| ≤ Γ1 / 2 ^ 59 := by
    have hd : |Y - Real.log Γ1| ≤ 1 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]
    have h1 := Real.abs_exp_sub_one_le hd
    have hEY : Real.exp Y = Γ1 * Real.exp (Y - Real.log Γ1) := by
      rw [Real.exp_sub, Real.exp_log hΓ]
      field_simp
    rw [hEY, show Γ1 * Real.exp (Y - Real.log Γ1) - Γ1 = Γ1 * (Real.exp (Y - Real.log Γ1) - 1) by
      ring, abs_mul, abs_of_pos hΓ]
    calc Γ1 * |Real.exp (Y - Real.log Γ1) - 1| ≤ Γ1 * (2 * (1 / 2 ^ 60)) := by
          gcongr
          linarith
      _ = Γ1 / 2 ^ 59 := by ring
  have h1 := abs_sub_le Q (Real.exp Y) Γ1
  have h2 : Real.exp Y ≤ Γ1 + Γ1 / 2 ^ 59 := by linarith [(abs_le.mp hEG).2]
  linarith

/-- The quotient `Pc/Z` against `π/K` for `Z` within `a K` of `K` and `Pc` within `b` of `π`. -/
theorem ratio_err (K Z Pc a b : ℝ) (hK : 0 < K) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (hZ : |Z - K| ≤ a * K) (hb0 : 0 ≤ b) (hb : |Pc - Real.pi| ≤ b) :
    |Pc / Z - Real.pi / K| ≤ Real.pi / K * ((b / 3 + a) * (1 + 2 * a)) := by
  have hpi3 := Real.pi_gt_three
  have hZlo : K * (1 - a) ≤ Z := by linarith [(abs_le.mp hZ).1]
  have hZ0 : 0 < Z := lt_of_lt_of_le (by nlinarith) hZlo
  rw [div_sub_div _ _ hZ0.ne' hK.ne', abs_div, abs_of_pos (mul_pos hZ0 hK),
    div_le_iff₀ (mul_pos hZ0 hK)]
  have hnum : |Pc * K - Z * Real.pi| ≤ b * K + Real.pi * (a * K) := by
    rw [show Pc * K - Z * Real.pi = (Pc - Real.pi) * K + Real.pi * (K - Z) by ring]
    have := abs_add_le ((Pc - Real.pi) * K) (Real.pi * (K - Z))
    rw [abs_mul, abs_mul, abs_of_pos hK, abs_of_pos Real.pi_pos, abs_sub_comm K Z] at this
    have h1 : |Pc - Real.pi| * K ≤ b * K := mul_le_mul_of_nonneg_right hb hK.le
    have h2 : Real.pi * |Z - K| ≤ Real.pi * (a * K) := mul_le_mul_of_nonneg_left hZ Real.pi_pos.le
    linarith
  have hc0 : 0 ≤ b / 3 + a := by positivity
  have h3 : Real.pi / K * ((b / 3 + a) * (1 + 2 * a)) * (Z * K) =
      Real.pi * (b / 3 + a) * (1 + 2 * a) * Z := by
    field_simp
  rw [h3]
  have h4 : Real.pi * (b / 3 + a) * (1 + 2 * a) * (K * (1 - a)) ≤
      Real.pi * (b / 3 + a) * (1 + 2 * a) * Z :=
    mul_le_mul_of_nonneg_left hZlo (by positivity)
  have h5 : (1 + 2 * a) * (1 - a) ≥ 1 := by nlinarith
  have h6 : Real.pi * (b / 3 + a) * K ≤ Real.pi * (b / 3 + a) * (1 + 2 * a) * (K * (1 - a)) := by
    have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ Real.pi * (b / 3 + a) * K)
    nlinarith
  have h7 : b * K ≤ Real.pi * (b / 3) * K := by
    have : b ≤ Real.pi * (b / 3) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hK.le
  nlinarith

#print axioms grid
#print axioms sin_lower
#print axioms exp_close
#print axioms ratio_err

end Library.Numerics.Float64.Tgamma.TgammaRefl4
