import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Identities and elementary bounds of `Γ` that CORE-MATH's `tgamma` and `lgamma` use.  The shift
`Γ (x + n) = Γ x · x (x + 1) ⋯ (x + n - 1)` holds away from the poles, and `Γ (k + 1)` is the
product `1 · 2 ⋯ k`.  `lgamma x = log (Γ x)` is `log |Γ x|`, since `Real.log` takes the absolute
value of a negative argument; it satisfies `lgamma (x + 1) = lgamma x + log |x|` and vanishes at
1 and 2.  For non-integer `x` the reflection formula gives `Γ x = π / (sin (π x) Γ (1 - x))` and
`lgamma x + lgamma (1 - x) = log π - log |sin (π x)|`, and for `x < 1` the sign of `Γ x` is
`(-1) ^ ⌊x⌋`.  Jordan's inequality gives `|sin (π x)| ≥ 2 |x - round x|`.  The convexity of `Γ`
with `Γ (1/2) = √π` gives `-8/5 ≤ Γ x - 1/x ≤ 0` for nonzero `x` in `[-1/2, 1]`, hence
`|lgamma x + log |x|| ≤ 4 |x|` for `0 < |x| ≤ 1/4`.  For `x ≤ -184` at distance at least `2 ^ -45`
from the integers, as every non-integer double below -128 is, `|Γ x| < 2 ^ -1078`.
-/

namespace LeanExe.ProofKit.GammaBasic

open Real Finset

set_option exponentiation.threshold 2048

/-- `log |Γ x|`, C's `lgamma` away from the poles. -/
noncomputable def lgamma (x : ℝ) : ℝ := log (Gamma x)

/-- `x` is not a pole of `Γ`, that is, neither 0 nor a negative integer. -/
def NotPole (x : ℝ) : Prop := ∀ m : ℕ, x ≠ -m

theorem NotPole.add_nat {x : ℝ} (h : NotPole x) (n : ℕ) : NotPole (x + n) := by
  intro m hm
  apply h (m + n)
  push_cast
  linarith

theorem NotPole.ne_zero {x : ℝ} (h : NotPole x) : x ≠ 0 := by
  simpa using h 0

theorem notPole_of_neg_one_lt {x : ℝ} (hx : -1 < x) (h0 : x ≠ 0) : NotPole x := by
  intro m hm
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp at hm
    exact h0 hm
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    linarith

theorem notPole_of_not_int {x : ℝ} (h : ∀ n : ℤ, x ≠ n) : NotPole x := by
  intro m hm
  exact h (-(m : ℤ)) (by push_cast; exact hm)

theorem gamma_add_nat {x : ℝ} (h : NotPole x) (n : ℕ) :
    Gamma (x + n) = Gamma x * ∏ j ∈ range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, Nat.cast_succ, ← add_assoc, Gamma_add_one (h.add_nat n).ne_zero, ih]
    ring

theorem shift_prod_ne_zero {x : ℝ} (h : NotPole x) (n : ℕ) : ∏ j ∈ range n, (x + j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => (h.add_nat j).ne_zero

theorem gamma_eq_div {x : ℝ} (h : NotPole x) (n : ℕ) :
    Gamma x = Gamma (x + n) / ∏ j ∈ range n, (x + j) := by
  rw [gamma_add_nat h n, mul_div_cancel_right₀ _ (shift_prod_ne_zero h n)]

theorem gamma_nat_prod (k : ℕ) : Gamma (k + 1) = ∏ i ∈ range k, ((i : ℝ) + 1) := by
  rw [Gamma_nat_eq_factorial, ← prod_range_add_one_eq_factorial, Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

theorem lgamma_add_one {x : ℝ} (h : NotPole x) : lgamma (x + 1) = lgamma x + log x := by
  rw [lgamma, lgamma, Gamma_add_one h.ne_zero, log_mul h.ne_zero (Gamma_ne_zero h), add_comm]

theorem lgamma_one : lgamma 1 = 0 := by simp [lgamma, Gamma_one]

theorem lgamma_two : lgamma 2 = 0 := by simp [lgamma]

theorem sin_pi_ne_zero {x : ℝ} (h : ∀ n : ℤ, x ≠ n) : sin (π * x) ≠ 0 := by
  intro hs
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp hs
  exact h n (mul_left_cancel₀ pi_ne_zero (by rw [← hn]; ring))

theorem gamma_one_sub_ne_zero {x : ℝ} (h : ∀ n : ℤ, x ≠ n) : Gamma (1 - x) ≠ 0 := by
  apply Gamma_ne_zero
  intro m hm
  exact h (m + 1) (by push_cast; linarith)

theorem gamma_reflect {x : ℝ} (h : ∀ n : ℤ, x ≠ n) :
    Gamma x = π / (sin (π * x) * Gamma (1 - x)) := by
  have hs := sin_pi_ne_zero h
  rw [eq_div_iff (mul_ne_zero hs (gamma_one_sub_ne_zero h))]
  calc Gamma x * (sin (π * x) * Gamma (1 - x))
      = Gamma x * Gamma (1 - x) * sin (π * x) := by ring
    _ = π := by rw [Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hs]

theorem lgamma_reflect {x : ℝ} (h : ∀ n : ℤ, x ≠ n) :
    lgamma x + lgamma (1 - x) = log π - log (sin (π * x)) := by
  rw [lgamma, lgamma, ← log_mul (Gamma_ne_zero (notPole_of_not_int h)) (gamma_one_sub_ne_zero h),
    Gamma_mul_Gamma_one_sub, log_div pi_ne_zero (sin_pi_ne_zero h)]

theorem sin_pi_eq (x : ℝ) : sin (π * x) = (-1) ^ ⌊x⌋ * sin (π * Int.fract x) := by
  rw [← sin_add_int_mul_pi, ← Int.self_sub_floor]
  congr 1
  ring

theorem sin_pi_fract_pos {x : ℝ} (h : ∀ n : ℤ, x ≠ n) : 0 < sin (π * Int.fract x) := by
  have hf : 0 < Int.fract x := by
    rcases (Int.fract_nonneg x).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have he := Int.fract_add_floor x
      rw [← heq] at he
      exact h ⌊x⌋ (by linarith)
  exact sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hf)
    (mul_lt_of_lt_one_right pi_pos (Int.fract_lt_one x))

theorem gamma_pos_of_even {x : ℝ} (hx : x < 1) (h : ∀ n : ℤ, x ≠ n) (he : Even ⌊x⌋) :
    0 < Gamma x := by
  rw [gamma_reflect h, sin_pi_eq, he.neg_one_zpow, one_mul]
  exact div_pos pi_pos (mul_pos (sin_pi_fract_pos h) (Gamma_pos_of_pos (by linarith)))

theorem gamma_neg_of_odd {x : ℝ} (hx : x < 1) (h : ∀ n : ℤ, x ≠ n) (ho : Odd ⌊x⌋) :
    Gamma x < 0 := by
  rw [gamma_reflect h, sin_pi_eq, ho.neg_one_zpow, neg_one_mul, neg_mul]
  exact div_neg_of_pos_of_neg pi_pos
    (neg_neg_of_pos (mul_pos (sin_pi_fract_pos h) (Gamma_pos_of_pos (by linarith))))

theorem two_mul_abs_sub_round_le (x : ℝ) : 2 * |x - round x| ≤ |sin (π * x)| := by
  have hs : sin (π * x) = (-1) ^ round x * sin (π * (x - round x)) := by
    rw [← sin_add_int_mul_pi]
    congr 1
    ring
  rw [hs, abs_mul, abs_neg_one_zpow, one_mul]
  have hd2 : |x - round x| ≤ 1 / 2 := abs_sub_round x
  have hnn : 0 ≤ sin (π * |x - round x|) :=
    sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
  have he : |sin (π * (x - round x))| = sin (π * |x - round x|) := by
    rw [← abs_of_nonneg hnn]
    rcases abs_choice (x - round x) with h | h
    · rw [h]
    · rw [h, mul_neg, sin_neg, abs_neg]
  rw [he]
  have hj := mul_le_sin (x := π * |x - round x|) (by positivity) (by nlinarith [pi_pos])
  have hc : 2 / π * (π * |x - round x|) = 2 * |x - round x| := by
    field_simp
  linarith

theorem abs_gamma_le {x : ℝ} (h : ∀ n : ℤ, x ≠ n) (hx : x < 1) :
    |Gamma x| ≤ π / (2 * |x - round x| * Gamma (1 - x)) := by
  have hg : 0 < Gamma (1 - x) := Gamma_pos_of_pos (by linarith)
  have hd : 0 < |x - round x| := by
    apply abs_pos.mpr
    intro h0
    exact h (round x) (by linarith)
  rw [gamma_reflect h, abs_div, abs_of_pos pi_pos, abs_mul, abs_of_pos hg]
  apply div_le_div_of_nonneg_left pi_pos.le (by positivity)
  exact mul_le_mul_of_nonneg_right (two_mul_abs_sub_round_le x) hg.le

theorem factorial_184 : (315 : ℝ) * 2 ^ 1122 < 100 * (Nat.factorial 184 : ℝ) := by
  have h : (315 : ℕ) * 2 ^ 1122 < 100 * Nat.factorial 184 := by decide +kernel
  exact_mod_cast h

theorem gamma_underflow {x : ℝ} (hx : x ≤ -184) (hd : 1 / 2 ^ 45 ≤ |x - round x|) :
    |Gamma x| < 1 / 2 ^ 1078 := by
  have hint : ∀ n : ℤ, x ≠ n := by
    intro n hn
    have : |x - round x| = 0 := by rw [hn, round_intCast, sub_self, abs_zero]
    have : (0 : ℝ) < 1 / 2 ^ 45 := by positivity
    linarith
  have hmono : Gamma 185 ≤ Gamma (1 - x) :=
    Gamma_strictMonoOn_Ici.monotoneOn (by norm_num [Set.mem_Ici])
      (by rw [Set.mem_Ici]; linarith) (by linarith)
  have h185 : Gamma 185 = (Nat.factorial 184 : ℝ) := by
    have h := Gamma_nat_eq_factorial 184
    rw [show ((184 : ℕ) : ℝ) + 1 = 185 by norm_num] at h
    exact h
  have hf := factorial_184
  have hpi := pi_lt_d2
  have hF : 0 < (Nat.factorial 184 : ℝ) := by positivity
  have hb := abs_gamma_le hint (by linarith)
  have hden : 2 * (1 / 2 ^ 45) * (Nat.factorial 184 : ℝ) ≤ 2 * |x - round x| * Gamma (1 - x) := by
    rw [← h185]
    apply mul_le_mul (by linarith) hmono (by rw [h185]; exact hF.le) (by positivity)
  have h1 : π / (2 * |x - round x| * Gamma (1 - x)) ≤ π / (2 * (1 / 2 ^ 45) * (Nat.factorial 184 : ℝ)) :=
    div_le_div_of_nonneg_left pi_pos.le (by positivity) hden
  have h2 : π / (2 * (1 / 2 ^ 45) * (Nat.factorial 184 : ℝ)) < 1 / 2 ^ 1078 := by
    have e : 2 * (1 / (2 : ℝ) ^ 45) * (Nat.factorial 184 : ℝ) =
        (Nat.factorial 184 : ℝ) / 2 ^ 44 := by
      rw [show (2 : ℝ) ^ 45 = 2 * 2 ^ 44 by ring]
      field_simp
    rw [e, div_div_eq_mul_div, div_lt_div_iff₀ hF (by positivity), mul_assoc, ← pow_add,
      one_mul]
    rw [show 44 + 1078 = 1122 by norm_num]
    have hm := mul_lt_mul_of_pos_right hpi (by positivity : (0 : ℝ) < 2 ^ 1122)
    rw [show (3.15 : ℝ) = 315 / 100 by norm_num] at hm
    generalize (2 : ℝ) ^ 1122 = P at *
    linarith
  linarith

theorem gamma_sub_inv_bounds {x : ℝ} (hx : x ≠ 0) (hlo : -1 / 2 ≤ x) (hhi : x ≤ 1) :
    -8 / 5 ≤ Gamma x - 1 / x ∧ Gamma x - 1 / x ≤ 0 := by
  have hkey : Gamma x - 1 / x = (Gamma (1 + x) - Gamma 1) / ((1 + x) - 1) := by
    rw [add_comm 1 x, Gamma_add_one hx, Gamma_one, add_sub_cancel_right, sub_div,
      mul_div_cancel_left₀ _ hx]
  have hmem : (1 + x) ∈ Set.Ioi (0 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hx1 : (1 + x) ≠ 1 := by
    intro h
    apply hx
    linarith
  have hup := convexOn_Gamma.secant_mono (a := 1) (x := 1 + x) (y := 2)
    (by norm_num) hmem (by norm_num) hx1 (by norm_num) (by linarith)
  have hlow := convexOn_Gamma.secant_mono (a := 1) (x := 1 / 2) (y := 1 + x)
    (by norm_num) (by norm_num) hmem (by norm_num) hx1 (by linarith)
  rw [Gamma_two, Gamma_one] at hup
  rw [Gamma_one_half_eq, Gamma_one] at hlow
  have hsq : √π < 9 / 5 := by
    rw [sqrt_lt' (by norm_num)]
    have := pi_lt_d2
    norm_num at this ⊢
    linarith
  have hl : (√π - 1) / (1 / 2 - 1) = 2 - 2 * √π := by ring
  rw [hl] at hlow
  have hz : ((1 : ℝ) - 1) / (2 - 1) = 0 := by norm_num
  rw [hz] at hup
  rw [hkey, Gamma_one]
  constructor
  · linarith
  · exact hup

theorem abs_lgamma_add_log_le {x : ℝ} (hx : x ≠ 0) (hb : |x| ≤ 1 / 4) :
    |lgamma x + log x| ≤ 4 * |x| := by
  have hab := abs_le.mp hb
  have hnp := notPole_of_neg_one_lt (by linarith) hx
  rw [← lgamma_add_one hnp, lgamma]
  obtain ⟨hs1, hs2⟩ := gamma_sub_inv_bounds hx (by linarith) (by linarith)
  have hg : Gamma (x + 1) - 1 = x * (Gamma x - 1 / x) := by
    rw [Gamma_add_one hx]
    field_simp
  have hd : |Gamma (x + 1) - 1| ≤ 8 / 5 * |x| := by
    rw [hg, abs_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
    rw [abs_le]
    constructor <;> linarith
  have hax : 8 / 5 * |x| ≤ 2 / 5 := by linarith
  have hy := abs_le.mp hd
  have hpos : 0 < Gamma (x + 1) := by linarith
  have hu := log_le_sub_one_of_pos hpos
  have hl := one_sub_inv_le_log_of_pos hpos
  have hinv : (Gamma (x + 1))⁻¹ ≤ 1 + 2 * (8 / 5 * |x|) := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg (show 0 ≤ 8 / 5 * |x| by positivity)
        (show 0 ≤ 2 / 5 - 8 / 5 * |x| by linarith),
      mul_nonneg (show 0 ≤ Gamma (x + 1) - 1 + 8 / 5 * |x| by linarith)
        (show 0 ≤ 1 + 2 * (8 / 5 * |x|) by positivity)]
  rw [abs_le]
  constructor <;> linarith

#print axioms gamma_add_nat
#print axioms gamma_eq_div
#print axioms gamma_nat_prod
#print axioms lgamma_add_one
#print axioms lgamma_one
#print axioms lgamma_two
#print axioms gamma_reflect
#print axioms lgamma_reflect
#print axioms gamma_pos_of_even
#print axioms gamma_neg_of_odd
#print axioms two_mul_abs_sub_round_le
#print axioms abs_gamma_le
#print axioms gamma_underflow
#print axioms gamma_sub_inv_bounds
#print axioms abs_lgamma_add_log_le

end LeanExe.ProofKit.GammaBasic
