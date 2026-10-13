import Verified.Examples.BesselRecur
import Verified.Examples.BesselY1Large
import Verified.Examples.TrigNear

/-!
`jn` and `yn` from `2^302` on, where the code returns Hankel's leading term
`invsqrtpi · phaseCos (n mod 4) (sin x) (cos x) / √x` or the same with `phaseSin`.  With
`λ_k = 2k/x ≤ 2^-269` for `k ≤ 2^32`, the recurrence 10.6.1 keeps `G_n` within `n 2^-268 (|G₀| + |G₁|)`
of the pattern `(-1) ^ (n/2) G_(n mod 2)` for `G = J` or `Y` (`pattern_close`).  The pattern is
`±J₀`, `±J₁`, `±Y₀`, or `±Y₁`, which the forms of `BesselCombine` write as
`σ (P A - Q B)/√(π x)` with `A² + B² = 2`, and `phaseCos` and `phaseSin` compute `σ A` within
`4.27 u` from `TrigNear.sin_near` and `cos_near` (`bracket_cos`, `bracket_sin`).
`BesselCase.case_one` with the bounds `BesselLarge.huge_pq0` and `huge_pq1` on `P - 1` and `Q`
then gives `10 u M` against the pattern, and the deviation adds less than `u M` (`jn_hankel`,
`yn_hankel`).
-/

namespace Verified.Examples.BesselOrderHuge
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselCombine BesselCase
  BesselLarge BesselJ0Large BesselY1Large BesselCS TrigNear Real BesselOrderN BesselRecur
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)
open LeanExe.ProofKit.BesselPQ (P0 Q0 P1 Q1 modulus0 modulus1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The pattern `(-1) ^ (k/2) G_(k mod 2)`. -/
noncomputable def pat (G : ℕ → ℝ) (k : ℕ) : ℝ := (-1) ^ (k / 2) * G (k % 2)

theorem pat_succ_succ (G : ℕ → ℝ) (k : ℕ) : pat G (k + 2) = -pat G k := by
  simp only [pat, show (k + 2) / 2 = k / 2 + 1 by omega, show (k + 2) % 2 = k % 2 by omega,
    pow_succ]
  ring

theorem abs_pat_le (G : ℕ → ℝ) (k : ℕ) : |pat G k| ≤ |G 0| + |G 1| := by
  simp only [pat, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;>
    linarith [abs_nonneg (G 0), abs_nonneg (G 1)]

/-- A solution of 10.6.1 stays near its pattern while `λ_k ≤ 2^-269`. -/
theorem pattern_close (x : ℝ) (hx : 2 ^ 302 ≤ x) (G : ℕ → ℝ)
    (hG : ∀ k, G (k + 2) = 2 * (k + 1) / x * G (k + 1) - G k) :
    ∀ k, k ≤ 2 ^ 32 → |G k - pat G k| ≤ k / 2 ^ 268 * (|G 0| + |G 1|) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hA : 0 ≤ |G 0| + |G 1| := by positivity
  have key : ∀ k, k + 1 ≤ 2 ^ 32 → |G k - pat G k| ≤ k / 2 ^ 268 * (|G 0| + |G 1|) ∧
      |G (k + 1) - pat G (k + 1)| ≤ (k + 1 : ℕ) / 2 ^ 268 * (|G 0| + |G 1|) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [pat]
      exact hA
    | succ m ih =>
      intro hm
      obtain ⟨h0, h1⟩ := ih (by omega)
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [show m + 1 + 1 = m + 2 by ring, hG m, pat_succ_succ]
      have hlam : 2 * ((m : ℝ) + 1) / x ≤ 1 / 2 ^ 269 := by
        rw [div_le_iff₀ hx0]
        have : (m : ℝ) + 1 ≤ 2 ^ 32 := by exact_mod_cast (show m + 1 ≤ 2 ^ 32 by omega)
        have e : (1 : ℝ) / 2 ^ 269 * 2 ^ 302 = 2 * 2 ^ 32 := by norm_num
        nlinarith
      have hlam0 : 0 ≤ 2 * ((m : ℝ) + 1) / x := by positivity
      have hp := abs_pat_le G (m + 1)
      have hd1 : |G (m + 1)| ≤ 2 * (|G 0| + |G 1|) := by
        have : (((m + 1 : ℕ) : ℝ) / 2 ^ 268) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast (show m + 1 ≤ 2 ^ 268 by omega)
        have := abs_sub_abs_le_abs_sub (G (m + 1)) (pat G (m + 1))
        nlinarith
      have hstep : |2 * ((m : ℝ) + 1) / x * G (m + 1) - G m - -pat G m| ≤
          2 * ((m : ℝ) + 1) / x * |G (m + 1)| + |G m - pat G m| := by
        have := abs_add_le (2 * ((m : ℝ) + 1) / x * G (m + 1)) (-(G m - pat G m))
        rw [abs_mul, abs_of_nonneg hlam0, abs_neg] at this
        have e : 2 * ((m : ℝ) + 1) / x * G (m + 1) - G m - -pat G m =
            2 * ((m : ℝ) + 1) / x * G (m + 1) + -(G m - pat G m) := by ring
        rw [e]
        exact this
      have h3 : 2 * ((m : ℝ) + 1) / x * |G (m + 1)| ≤ 1 / 2 ^ 269 * (2 * (|G 0| + |G 1|)) :=
        mul_le_mul hlam hd1 (abs_nonneg _) (by norm_num)
      push_cast at h0 ⊢
      have e : (1 : ℝ) / 2 ^ 269 * (2 * (|G 0| + |G 1|)) = 1 / 2 ^ 268 * (|G 0| + |G 1|) := by
        ring
      nlinarith
  intro k hk
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp [pat]
  · have := (key (k - 1) (by omega)).2
    rw [show k - 1 + 1 = k by omega] at this
    exact this

/-- The four brackets of `phaseCos`. -/
theorem bracket_cos (k : UInt64) (s c : Float) (S C : ℝ) (hs : FApprox s S trigErr)
    (hc : FApprox c C trigErr) (hSC : (S + C) ^ 2 + (S - C) ^ 2 = 2) :
    FApprox (Bessel.phaseCos k s c)
      (if k == 0 then C + S else if k == 1 then -C + S else if k == 2 then -C - S else C - S)
      (427 / 100 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have ht : trigErr = 71 / 50 * 𝐮 := rfl
  have hA := abs_le_sqrt_two (show (S + C) ^ 2 ≤ 2 by nlinarith [sq_nonneg (S - C)])
  have hB := abs_le_sqrt_two (show (S - C) ^ 2 ≤ 2 by nlinarith [sq_nonneg (S + C)])
  unfold Bessel.phaseCos
  split_ifs
  · have h := fapprox_add hc hs (14143 / 10000 + 2 * trigErr) (by
      rw [show C + S = S + C by ring]; linarith) (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)
  · have h := fapprox_add (fapprox_neg hc) hs (14143 / 10000 + 2 * trigErr) (by
      rw [show -C + S = S - C by ring]; linarith) (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)
  · have h := fapprox_sub (fapprox_neg hc) hs (14143 / 10000 + 2 * trigErr) (by
      rw [show -C - S = -(S + C) by ring, abs_neg]; linarith) (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)
  · have h := fapprox_sub hc hs (14143 / 10000 + 2 * trigErr) (by
      rw [show C - S = -(S - C) by ring, abs_neg]; linarith) (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)

/-- The four brackets of `phaseSin`. -/
theorem bracket_sin (k : UInt64) (s c : Float) (S C : ℝ) (hs : FApprox s S trigErr)
    (hc : FApprox c C trigErr) (hSC : (S + C) ^ 2 + (S - C) ^ 2 = 2) :
    FApprox (Bessel.phaseSin k s c)
      (if k == 0 then S - C else if k == 1 then -S - C else if k == 2 then -S + C else S + C)
      (427 / 100 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have ht : trigErr = 71 / 50 * 𝐮 := rfl
  have hA := abs_le_sqrt_two (show (S + C) ^ 2 ≤ 2 by nlinarith [sq_nonneg (S - C)])
  have hB := abs_le_sqrt_two (show (S - C) ^ 2 ≤ 2 by nlinarith [sq_nonneg (S + C)])
  unfold Bessel.phaseSin
  split_ifs
  · have h := fapprox_sub hs hc (14143 / 10000 + 2 * trigErr) (by linarith)
      (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)
  · have h := fapprox_sub (fapprox_neg hs) hc (14143 / 10000 + 2 * trigErr) (by
      rw [show -S - C = -(S + C) by ring, abs_neg]; linarith) (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)
  · have h := fapprox_add (fapprox_neg hs) hc (14143 / 10000 + 2 * trigErr) (by
      rw [show -S + C = -(S - C) by ring, abs_neg]; linarith) (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)
  · have h := fapprox_add hs hc (14143 / 10000 + 2 * trigErr) (by linarith)
      (by rw [ht, hu]; norm_num)
    exact fmono h (by rw [ht, hu]; norm_num)

/-- `σ (P A - Q B)/√(π w)` against the computed bracket. -/
theorem huge_case {c xa : Float} {A B P Q σ F M : ℝ} (hσ : |σ| = 1)
    (hc : FApprox c (σ * A) (427 / 100 * 𝐮)) (hAB : A ^ 2 + B ^ 2 = 2)
    (hP : |P - 1| ≤ 283 / 2 ^ 68) (hQ : |Q| ≤ 21 / 2 ^ 68) (hxf : Finite xa.toBits)
    (hw : 2 ^ 302 ≤ value xa.toBits) (hwb : value xa.toBits ≤ 2 ^ 1024)
    (hF : F = σ * (P * A - Q * B) / √(π * value xa.toBits))
    (hM : 7978 / 10000 * (9 / 10) / √(value xa.toBits) ≤ M) :
    Finite (Bessel.invsqrtpi * c / xa.sqrt).toBits ∧
      |value (Bessel.invsqrtpi * c / xa.sqrt).toBits - F| ≤ 10 * 𝐮 * M := by
  have hA := abs_le_sqrt_two (show A ^ 2 ≤ 2 by nlinarith [sq_nonneg B])
  have hB := abs_le_sqrt_two (show B ^ 2 ≤ 2 by nlinarith [sq_nonneg A])
  have hTA : |σ * A - σ * (P * A - Q * B)| ≤ (283 / 2 ^ 68 + 21 / 2 ^ 68) * (14143 / 10000) := by
    rw [show σ * A - σ * (P * A - Q * B) = σ * (-(P - 1) * A + Q * B) by ring, abs_mul, hσ,
      one_mul]
    have := abs_add_le (-(P - 1) * A) (Q * B)
    rw [abs_mul, abs_mul, abs_neg] at this
    have e1 := mul_le_mul hP hA (abs_nonneg _) (by norm_num)
    have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
    linarith
  have hMT : |σ * (P * A - Q * B)| ≤ (1 + 283 / 2 ^ 68) * (14143 / 10000) +
      21 / 2 ^ 68 * (14143 / 10000) := by
    rw [abs_mul, hσ, one_mul]
    have hP' : |P| ≤ 1 + 283 / 2 ^ 68 := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have := abs_sub (P * A) (Q * B)
    rw [abs_mul, abs_mul] at this
    have e1 := mul_le_mul hP' hA (abs_nonneg _) (by norm_num)
    have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
    linarith
  have hx2 : 2 ≤ value xa.toBits := le_trans (by norm_num) hw
  have h := case_one (K := 10) hc hTA hMT (by norm_num [unitRoundoff64])
    (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64]) (by norm_num) hxf hx2 hwb hM
  rw [hF]
  exact h

/-- `√(c² + d²) ≤ √(a² + b²) + |c - a| + |d - b|`. -/
theorem sqrt_dev (a b c d : ℝ) : √(c ^ 2 + d ^ 2) ≤ √(a ^ 2 + b ^ 2) + |c - a| + |d - b| := by
  have hr := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  have hrs := Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
  have ha : |a| ≤ √(a ^ 2 + b ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg b])
  have hb : |b| ≤ √(a ^ 2 + b ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg a])
  have hc : |c| ≤ |a| + |c - a| := by
    have := abs_add_le a (c - a); rw [show a + (c - a) = c by ring] at this; exact this
  have hd : |d| ≤ |b| + |d - b| := by
    have := abs_add_le b (d - b); rw [show b + (d - b) = d by ring] at this; exact this
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hp := abs_nonneg (c - a)
  have hq := abs_nonneg (d - b)
  have hc2 : c ^ 2 ≤ (|a| + |c - a|) ^ 2 := by
    rw [← sq_abs c]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have hd2 : d ^ 2 ≤ (|b| + |d - b|) ^ 2 := by
    rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hab : |a| * |c - a| + |b| * |d - b| ≤ √(a ^ 2 + b ^ 2) * (|c - a| + |d - b|) := by
    nlinarith
  nlinarith [sq_abs a, sq_abs b]

/-- The pattern of `G` at `n` with `n mod 4` known. -/
theorem pat_eval (G : ℕ → ℝ) (n : ℕ) :
    (n % 4 = 0 → pat G n = G 0) ∧ (n % 4 = 1 → pat G n = G 1) ∧
      (n % 4 = 2 → pat G n = -G 0) ∧ (n % 4 = 3 → pat G n = -G 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> unfold pat
  · rw [show n % 2 = 0 by omega, (show Even (n / 2) from ⟨n / 4, by omega⟩).neg_one_pow, one_mul]
  · rw [show n % 2 = 1 by omega, (show Even (n / 2) from ⟨n / 4, by omega⟩).neg_one_pow, one_mul]
  · rw [show n % 2 = 0 by omega, (show Odd (n / 2) from ⟨n / 4, by omega⟩).neg_one_pow]; ring
  · rw [show n % 2 = 1 by omega, (show Odd (n / 2) from ⟨n / 4, by omega⟩).neg_one_pow]; ring

theorem and_three (n : UInt64) : (n &&& 3).toNat = n.toNat % 4 := by
  rw [UInt64.toNat_and]
  change n.toNat &&& (2 ^ 2 - 1) = n.toNat % 2 ^ 2
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- The bounds of the orders 0 and 1 from `2^302` on. -/
theorem base_bounds (w : ℝ) (hw : 2 ^ 302 ≤ w) :
    |J0 w| ≤ 1 / √w ∧ |J1 w| ≤ 1 / √w ∧ |Y0 w| ≤ 1 / √w ∧ |Y1 w| ≤ 1 / √w ∧
      7978 / 10000 * (1 - 283 / 2 ^ 68) / √w ≤ √(J0 w ^ 2 + Y0 w ^ 2) ∧
      7978 / 10000 * (1 - 283 / 2 ^ 68) / √w ≤ √(J1 w ^ 2 + Y1 w ^ 2) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have h129 : (2 : ℝ) ^ 129 ≤ w := le_trans (by norm_num) hw
  obtain ⟨hP0, hQ0⟩ := huge_pq0 w h129
  obtain ⟨hP1, hQ1⟩ := huge_pq1 w h129
  have hAB := sum_sq w
  have hA := abs_le_sqrt_two (show (sin w + cos w) ^ 2 ≤ 2 by nlinarith [sq_nonneg (sin w - cos w)])
  have hB := abs_le_sqrt_two (show (sin w - cos w) ^ 2 ≤ 2 by nlinarith [sq_nonneg (sin w + cos w)])
  have hB' : |-sin w - cos w| ≤ 14143 / 10000 := by
    rw [show -sin w - cos w = -(sin w + cos w) by ring, abs_neg]; exact hA
  have hpi : 3 < π := pi_gt_three
  have hsq : √(π * w) = √π * √w := Real.sqrt_mul (by positivity) w
  have hspi : 17 / 10 ≤ √π := by
    rw [show (17 / 10 : ℝ) = √((17 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw0
  have form_le : ∀ (P Q A B : ℝ), |P - 1| ≤ 283 / 2 ^ 68 → |Q| ≤ 21 / 2 ^ 68 →
      |A| ≤ 14143 / 10000 → |B| ≤ 14143 / 10000 →
      |(P * A - Q * B) / √(π * w)| ≤ 1 / √w := by
    intro P Q A B hP hQ hA hB
    have hP' : |P| ≤ 1 + 283 / 2 ^ 68 := by
      have := abs_sub_abs_le_abs_sub P 1; rw [abs_one] at this; linarith
    have h1 : |P * A - Q * B| ≤ 17 / 10 := by
      have := abs_sub (P * A) (Q * B)
      rw [abs_mul, abs_mul] at this
      have e1 := mul_le_mul hP' hA (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
      norm_num at e1 e2 ⊢
      linarith
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (by positivity)), hsq, div_le_div_iff₀
      (by positivity) hsw]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [J0_form w hw0]; exact form_le _ _ _ _ (by linarith) (by linarith) hA hB
  · rw [J1_form w hw0]; exact form_le _ _ _ _ hP1 hQ1 hB hB'
  · rw [Y0_form w hw0, show P0 w * (sin w - cos w) + Q0 w * (sin w + cos w) =
      P0 w * (sin w - cos w) - (-Q0 w) * (sin w + cos w) by ring]
    exact form_le _ _ _ _ (by linarith) (by rw [abs_neg]; linarith) hB hA
  · rw [Y1_form w hw0, show P1 w * (-sin w - cos w) + Q1 w * (sin w - cos w) =
      P1 w * (-sin w - cos w) - (-Q1 w) * (sin w - cos w) by ring]
    exact form_le _ _ _ _ hP1 (by rw [abs_neg]; linarith) hB' hB
  · exact modulus_ge hw0 (by norm_num) (by linarith [(abs_le.mp hP0).1]) (modulus0 w hw0)
  · exact modulus_ge hw0 (by norm_num) (by linarith [(abs_le.mp hP1).1]) (modulus1 w hw0)

/-- The pattern's distance and the modulus from `2^302` on. -/
theorem huge_dev (w : ℝ) (hw : 2 ^ 302 ≤ w) (n : ℕ) (hn : n ≤ 2 ^ 32) :
    |Jn n w - pat (fun k => Jn k w) n| ≤ 1 / 2 ^ 235 / √w ∧
      |Yn w n - pat (Yn w) n| ≤ 1 / 2 ^ 235 / √w ∧
      7978 / 10000 * (9 / 10) / √w ≤ modn w n := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := base_bounds w hw
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw0
  have hn' : (n : ℝ) / 2 ^ 268 ≤ 2 ^ 32 / 2 ^ 268 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hn) (by positivity)
  have dev : ∀ G : ℕ → ℝ, (∀ k, G (k + 2) = 2 * (k + 1) / w * G (k + 1) - G k) →
      |G 0| ≤ 1 / √w → |G 1| ≤ 1 / √w → |G n - pat G n| ≤ 1 / 2 ^ 235 / √w := by
    intro G hG h0 h1
    have h := pattern_close w hw G hG n hn
    have hs : |G 0| + |G 1| ≤ 2 / √w := by
      rw [show (2 : ℝ) / √w = 1 / √w + 1 / √w by ring]; linarith
    calc |G n - pat G n| ≤ n / 2 ^ 268 * (|G 0| + |G 1|) := h
      _ ≤ 2 ^ 32 / 2 ^ 268 * (2 / √w) := mul_le_mul hn' hs (by positivity) (by positivity)
      _ = 1 / 2 ^ 235 / √w := by ring
  have hJ := dev (fun k => Jn k w) (fun k => Jn_recur k w hw0.ne')
    (by simp only [Jn_zero]; exact b0) (by simp only [Jn_one]; exact b1)
  have hY := dev (Yn w) (fun k => Yn_recur w k) b2 b3
  refine ⟨hJ, hY, ?_⟩
  have hd := sqrt_dev (Jn n w) (Yn w n) (pat (fun k => Jn k w) n) (pat (Yn w) n)
  rw [abs_sub_comm (pat (fun k => Jn k w) n), abs_sub_comm (pat (Yn w) n)] at hd
  have hsq : ∀ (k : ℕ) (a : ℝ), ((-1 : ℝ) ^ k * a) ^ 2 = a ^ 2 := by
    intro k a
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow, one_mul]
  have hpat : pat (fun k => Jn k w) n ^ 2 + pat (Yn w) n ^ 2 =
      Jn (n % 2) w ^ 2 + Yn w (n % 2) ^ 2 := by
    simp only [pat, hsq]
  have hlow : 7978 / 10000 * (1 - 283 / 2 ^ 68) / √w ≤
      √(Jn (n % 2) w ^ 2 + Yn w (n % 2) ^ 2) := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h]
    · rw [Jn_zero, Yn_zero]
      exact le_trans (div_le_div_of_nonneg_right (by norm_num) hsw.le) b4
    · rw [Jn_one, Yn_one]; exact b5
  rw [hpat] at hd
  have key : 7978 / 10000 * (9 / 10) / √w + 1 / 2 ^ 235 / √w + 1 / 2 ^ 235 / √w ≤
      7978 / 10000 * (1 - 283 / 2 ^ 68) / √w := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hsw.le
  unfold modn
  linarith

/-- The last step: the pattern's error plus its distance. -/
theorem finish {r : Float} {F T M w : ℝ} (hw0 : 0 < w)
    (h : Finite r.toBits ∧ |value r.toBits - F| ≤ 10 * 𝐮 * M)
    (hd : |T - F| ≤ 1 / 2 ^ 235 / √w) (hM : 7978 / 10000 * (9 / 10) / √w ≤ M) :
    Finite r.toBits ∧ |value r.toBits - T| ≤ 11 * 𝐮 * M := by
  refine ⟨h.1, ?_⟩
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw0
  have hu : 1 / 2 ^ 235 / √w ≤ 𝐮 * (7978 / 10000 * (9 / 10) / √w) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by norm_num [unitRoundoff64]) hsw.le
  have hu2 := mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ 𝐮 by norm_num [unitRoundoff64])
  have := abs_sub_le (value r.toBits) F T
  rw [abs_sub_comm F T] at this
  linarith [h.2]

theorem and_three_eq (n m : UInt64) (h : n.toNat % 4 = m.toNat) : n &&& 3 = m :=
  UInt64.toNat_inj.mp (by rw [and_three, h])

/-- `jn` from `2^302` on, for the orders `|n| ≤ 2^32`. -/
theorem jn_hankel (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hw : 2 ^ 302 ≤ value xa.toBits) (hwb : value xa.toBits ≤ 2 ^ 1024) (hn : n.toNat ≤ 2 ^ 32) :
    Finite (Bessel.invsqrtpi * Bessel.phaseCos (n &&& 3) (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa) / xa.sqrt).toBits ∧
      |value (Bessel.invsqrtpi * Bessel.phaseCos (n &&& 3)
        (Trig.sinWith Trig.invPi Trig.halfPi xa) (Trig.cosWith Trig.invPi Trig.halfPi xa) /
          xa.sqrt).toBits - Jn n.toNat (value xa.toBits)| ≤
        11 * 𝐮 * modn (value xa.toBits) n.toNat := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  obtain ⟨hJd, -, hM⟩ := huge_dev w hw n.toNat hn
  have hs : FApprox (Trig.sinWith Trig.invPi Trig.halfPi xa) (Real.sin w) trigErr := sin_near xa hxf
  have hc : FApprox (Trig.cosWith Trig.invPi Trig.halfPi xa) (Real.cos w) trigErr := cos_near xa hxf
  have hb := bracket_cos (n &&& 3) _ _ _ _ hs hc (sum_sq w)
  have hpe := pat_eval (fun k => Jn k w) n.toNat
  obtain ⟨hP0, hQ0⟩ := huge_pq0 w (le_trans (by norm_num) hw)
  obtain ⟨hP1, hQ1⟩ := huge_pq1 w (le_trans (by norm_num) hw)
  have hP0' : |P0 w - 1| ≤ 283 / 2 ^ 68 := le_trans hP0 (by norm_num)
  have hQ0' : |Q0 w| ≤ 21 / 2 ^ 68 := le_trans hQ0 (by norm_num)
  refine finish hw0 ?_ hJd hM
  rcases (by omega : n.toNat % 4 = 0 ∨ n.toNat % 4 = 1 ∨ n.toNat % 4 = 2 ∨ n.toNat % 4 = 3)
    with h | h | h | h
  · have hk := and_three_eq n 0 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseCos 0 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (1 * (Real.sin w + Real.cos w)) (427 / 100 * 𝐮) :=
      fcongr hb (by show Real.cos w + Real.sin w = _; ring)
    refine huge_case (by norm_num) hb' (sum_sq w) hP0' hQ0' hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.1 h]
    simp only [Jn_zero, J0_form w hw0, one_mul]
  · have hk := and_three_eq n 1 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseCos 1 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (1 * (Real.sin w - Real.cos w)) (427 / 100 * 𝐮) :=
      fcongr hb (by show -Real.cos w + Real.sin w = _; ring)
    refine huge_case (by norm_num) hb' (sum_sq1 w) hP1 hQ1 hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.2.1 h]
    simp only [Jn_one, J1_form w hw0, one_mul]
  · have hk := and_three_eq n 2 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseCos 2 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (-1 * (Real.sin w + Real.cos w))
        (427 / 100 * 𝐮) :=
      fcongr hb (by show -Real.cos w - Real.sin w = _; ring)
    refine huge_case (by norm_num) hb' (sum_sq w) hP0' hQ0' hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.2.2.1 h]
    simp only [Jn_zero, J0_form w hw0]
    ring
  · have hk := and_three_eq n 3 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseCos 3 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (-1 * (Real.sin w - Real.cos w))
        (427 / 100 * 𝐮) :=
      fcongr hb (by show Real.cos w - Real.sin w = _; ring)
    refine huge_case (by norm_num) hb' (sum_sq1 w) hP1 hQ1 hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.2.2.2 h]
    simp only [Jn_one, J1_form w hw0]
    ring

/-- `yn` from `2^302` on, for the orders `|n| ≤ 2^32`. -/
theorem yn_hankel (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hw : 2 ^ 302 ≤ value xa.toBits) (hwb : value xa.toBits ≤ 2 ^ 1024) (hn : n.toNat ≤ 2 ^ 32) :
    Finite (Bessel.invsqrtpi * Bessel.phaseSin (n &&& 3) (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa) / xa.sqrt).toBits ∧
      |value (Bessel.invsqrtpi * Bessel.phaseSin (n &&& 3)
        (Trig.sinWith Trig.invPi Trig.halfPi xa) (Trig.cosWith Trig.invPi Trig.halfPi xa) /
          xa.sqrt).toBits - Yn (value xa.toBits) n.toNat| ≤
        11 * 𝐮 * modn (value xa.toBits) n.toNat := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  obtain ⟨-, hYd, hM⟩ := huge_dev w hw n.toNat hn
  have hs : FApprox (Trig.sinWith Trig.invPi Trig.halfPi xa) (Real.sin w) trigErr := sin_near xa hxf
  have hc : FApprox (Trig.cosWith Trig.invPi Trig.halfPi xa) (Real.cos w) trigErr := cos_near xa hxf
  have hb := bracket_sin (n &&& 3) _ _ _ _ hs hc (sum_sq w)
  have hpe := pat_eval (Yn w) n.toNat
  obtain ⟨hP0, hQ0⟩ := huge_pq0 w (le_trans (by norm_num) hw)
  obtain ⟨hP1, hQ1⟩ := huge_pq1 w (le_trans (by norm_num) hw)
  have hP0' : |P0 w - 1| ≤ 283 / 2 ^ 68 := le_trans hP0 (by norm_num)
  have hQ0' : |Q0 w| ≤ 21 / 2 ^ 68 := le_trans hQ0 (by norm_num)
  have hAB0 : (Real.sin w - Real.cos w) ^ 2 + (-(Real.sin w + Real.cos w)) ^ 2 = 2 := by
    linear_combination 2 * Real.sin_sq_add_cos_sq w
  have hAB1 : (-Real.sin w - Real.cos w) ^ 2 + (-(Real.sin w - Real.cos w)) ^ 2 = 2 := by
    linear_combination 2 * Real.sin_sq_add_cos_sq w
  refine finish hw0 ?_ hYd hM
  rcases (by omega : n.toNat % 4 = 0 ∨ n.toNat % 4 = 1 ∨ n.toNat % 4 = 2 ∨ n.toNat % 4 = 3)
    with h | h | h | h
  · have hk := and_three_eq n 0 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseSin 0 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (1 * (Real.sin w - Real.cos w)) (427 / 100 * 𝐮) :=
      fcongr hb (by show Real.sin w - Real.cos w = _; ring)
    refine huge_case (by norm_num) hb' hAB0 hP0' hQ0' hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.1 h]
    simp only [Yn_zero, Y0_form w hw0]
    ring
  · have hk := and_three_eq n 1 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseSin 1 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (1 * (-Real.sin w - Real.cos w))
        (427 / 100 * 𝐮) :=
      fcongr hb (by show -Real.sin w - Real.cos w = _; ring)
    refine huge_case (by norm_num) hb' hAB1 hP1 hQ1 hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.2.1 h]
    simp only [Yn_one, Y1_form w hw0]
    ring
  · have hk := and_three_eq n 2 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseSin 2 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (-1 * (Real.sin w - Real.cos w))
        (427 / 100 * 𝐮) :=
      fcongr hb (by show -Real.sin w + Real.cos w = _; ring)
    refine huge_case (by norm_num) hb' hAB0 hP0' hQ0' hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.2.2.1 h]
    simp only [Yn_zero, Y0_form w hw0]
    ring
  · have hk := and_three_eq n 3 (by rw [h]; rfl)
    rw [hk] at hb ⊢
    have hb' : FApprox (Bessel.phaseSin 3 (Trig.sinWith Trig.invPi Trig.halfPi xa)
        (Trig.cosWith Trig.invPi Trig.halfPi xa)) (-1 * (-Real.sin w - Real.cos w))
        (427 / 100 * 𝐮) :=
      fcongr hb (by show Real.sin w + Real.cos w = _; ring)
    refine huge_case (by norm_num) hb' hAB1 hP1 hQ1 hxf hw hwb ?_ hM
    rw [← hwdef]
    rw [hpe.2.2.2 h]
    simp only [Yn_one, Y1_form w hw0]
    ring

#print axioms pattern_close
#print axioms huge_dev
#print axioms jn_hankel
#print axioms yn_hankel

end Verified.Examples.BesselOrderHuge
