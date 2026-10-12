import LeanExe.ProofKit.GammaBasic
import LeanExe.ProofKit.PolyCalculus
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
Stirling's series for `lgamma` with a proved remainder bound.  For `x > 0` let
`F x = lgamma x - ((x - 1/2) log x - x + log (2 π)/2)`.  Then `F x - F (x + 1)` is
`φ x = (x + 1/2) log (1 + 1/x) - 1`, and `F (x + n) → 0` as `n → ∞`, from Mathlib's
`BohrMollerup.tendsto_log_gamma` and `Stirling.tendsto_stirlingSeq_sqrt_pi`.

For a coefficient list `cs` of length `m ≥ 1`, the series is `series cs x = x⁻¹ eval cs (x⁻²)`, and
the remainder `R x = F x - series cs x` satisfies `R x - R (x + 1) = ρ x`.  In `z = 1/x`,
`(1 + z) ^ (2 m - 1) ρ x` equals the polynomial `qpoly cs` at `z` plus a multiple of the remainder
of the logarithm's series of `2 m + 3` terms (`rho_identity`).  When the first `2 m + 2`
coefficients of `qpoly cs` vanish and `PolyBound.check` bounds the rest by `M` on `[0, z0]`,
`|ρ y| ≤ K y ^ -(2 m + 2)` for `y ≥ 1/z0` with `K = M + z0 (1 + z0/2)/(1 - z0)` (`abs_rho_le`).
The inequality `y ^ -(p + 1) ≤ (p (y - 1) ^ p)⁻¹ - (p y ^ p)⁻¹` telescopes, and the limit gives
`|R x| ≤ K / ((2 m + 1) (x - 1) ^ (2 m + 1))` (`abs_remainder_le`).  The instance `stirling_twelve`
uses the twelve coefficients `B (2 k)/(2 k (2 k - 1))`, `z0 = 1/16`, and `M = 104000`.
-/

namespace LeanExe.ProofKit.GammaStirling

open Real Filter Topology Finset PolyBound PolyChecks PolyCalculus TaylorRemainder GammaBasic

/-- The leading part `(x - 1/2) log x - x + log (2 π)/2` of Stirling's formula. -/
noncomputable def lead (x : ℝ) : ℝ := (x - 1 / 2) * log x - x + log (2 * π) / 2

/-- `lgamma x` minus the leading part. -/
noncomputable def F (x : ℝ) : ℝ := lgamma x - lead x

/-- The difference `F x - F (x + 1)`. -/
noncomputable def phi (x : ℝ) : ℝ := (x + 1 / 2) * log (1 + 1 / x) - 1

theorem F_sub_succ {x : ℝ} (hx : 0 < x) : F x - F (x + 1) = phi x := by
  have hnp := notPole_of_neg_one_lt (by linarith) hx.ne'
  have hl : log (1 + 1 / x) = log (x + 1) - log x := by
    rw [show 1 + 1 / x = (x + 1) / x by rw [add_div, div_self hx.ne'],
      log_div (by linarith) hx.ne']
  rw [F, F, lgamma_add_one hnp, phi, hl, lead, lead]
  ring

theorem lgamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    lgamma (x + n) = lgamma x + ∑ m ∈ range n, log (x + m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    rw [Nat.cast_succ, ← add_assoc, lgamma_add_one (notPole_of_neg_one_lt (by linarith) hxn.ne'),
      ih, sum_range_succ]
    ring

theorem tendsto_F {x : ℝ} (hx : 0 < x) : Tendsto (fun n : ℕ => F (x + n)) atTop (𝓝 0) := by
  have hG := BohrMollerup.tendsto_log_gamma hx
  have hS : Tendsto (fun n : ℕ => log (Stirling.stirlingSeq n)) atTop (𝓝 (log π / 2)) := by
    rw [← log_sqrt pi_pos.le]
    exact Stirling.tendsto_stirlingSeq_sqrt_pi.log (sqrt_pos.mpr pi_pos).ne'
  have hA : Tendsto (fun n : ℕ => (n : ℝ) * log (1 + (x + 1) / n)) atTop (𝓝 (x + 1)) :=
    (tendsto_mul_log_one_add_div_atTop (x + 1)).comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun n : ℕ => log (1 + (x + 1) / n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 + (x + 1) / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      (tendsto_const_div_atTop_nhds_zero_nat (x + 1)).const_add 1
    rw [add_zero] at h1
    have h2 := h1.log one_ne_zero
    rwa [log_one] at h2
  have hsum := ((tendsto_const_nhds (x := lgamma x)).sub hG).add
    ((hS.sub_const (log π / 2)).add
      ((tendsto_const_nhds (x := x + 1)).sub (hA.add (hB.const_mul (x + 1 / 2)))))
  have hlim : lgamma x - log (Gamma x) +
      (log π / 2 - log π / 2 + (x + 1 - (x + 1 + (x + 1 / 2) * 0))) = 0 := by
    rw [lgamma]
    ring
  rw [hlim] at hsum
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h1 : log (2 * (n : ℝ)) = log 2 + log n := log_mul two_ne_zero hnpos.ne'
  have h2 : log ((n : ℝ) / exp 1) = log n - 1 := by
    rw [log_div hnpos.ne' (exp_pos 1).ne', log_exp]
  have h3 : log (2 * π) = log 2 + log π := log_mul two_ne_zero pi_ne_zero
  have hxn : 0 < x + n + 1 := by linarith
  have h4 : log (1 + (x + 1) / n) = log (x + n + 1) - log n := by
    rw [show 1 + (x + 1) / n = (x + n + 1) / n by
      rw [eq_div_iff hnpos.ne', add_mul, div_mul_cancel₀ _ hnpos.ne']; ring,
      log_div hxn.ne' hnpos.ne']
  have h5 : lgamma (x + n + 1) = lgamma x + ∑ m ∈ range (n + 1), log (x + m) := by
    have h := lgamma_add_nat hx (n + 1)
    push_cast at h
    rwa [← add_assoc] at h
  have h6 : x + ((n + 1 : ℕ) : ℝ) = x + n + 1 := by
    push_cast
    ring
  rw [h6, BohrMollerup.logGammaSeq, Stirling.log_stirlingSeq_formula, F, lead, h1, h2, h3, h4, h5]
  ring

/-- The coefficients of `(1 + z) ^ N - (1 + z) ^ (N - 2 k - 1)` times `z ^ (2 k + 1)`. -/
def diffTerm (k N : ℕ) : List ℚ :=
  List.replicate (2 * k + 1) 0 ++ subP (powP [1, 1] N) (powP [1, 1] (N - 2 * k - 1))

/-- `Σ cs i · diffTerm (k + i) N`. -/
def diffSum : List ℚ → ℕ → ℕ → List ℚ
  | [], _, _ => []
  | c :: cs, k, N => addP (scaleP c (diffTerm k N)) (diffSum cs (k + 1) N)

/-- The polynomial whose value at `z = 1/y` is `(1 + z) ^ (2 m - 1) ρ y` up to the remainder of the
logarithm's series. -/
def qpoly (cs : List ℚ) : List ℚ :=
  subP (mulP (powP [1, 1] (2 * cs.length - 1))
      (addP (mulP [1, 1 / 2] (log1pQuotCoeffs (2 * cs.length + 3))) [-1]))
    (diffSum cs 0 (2 * cs.length - 1))

/-- `y ^ -(2 k + 1) eval cs (y⁻²)`. -/
noncomputable def seriesFrom (cs : List ℚ) (k : ℕ) (y : ℝ) : ℝ :=
  y⁻¹ ^ (2 * k + 1) * eval cs (y⁻¹ ^ 2)

/-- Stirling's series `Σ cs i y ^ -(2 i + 1)`. -/
noncomputable def series (cs : List ℚ) (y : ℝ) : ℝ := y⁻¹ * eval cs (y⁻¹ ^ 2)

/-- The difference `R y - R (y + 1)` of the remainders. -/
noncomputable def rho (cs : List ℚ) (y : ℝ) : ℝ := phi y - (series cs y - series cs (y + 1))

/-- The remainder of Stirling's series. -/
noncomputable def R (cs : List ℚ) (x : ℝ) : ℝ := F x - series cs x

theorem eval_one_one (z : ℝ) : eval [1, 1] z = 1 + z := by simp

theorem eval_diffTerm (k N : ℕ) (z : ℝ) :
    eval (diffTerm k N) z = z ^ (2 * k + 1) * ((1 + z) ^ N - (1 + z) ^ (N - 2 * k - 1)) := by
  rw [diffTerm, eval_replicate_append, eval_subP, eval_powP, eval_powP, eval_one_one]

theorem diffSum_eval (cs : List ℚ) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    ∀ k : ℕ, 2 * (k + cs.length) ≤ N + 1 →
      (1 + y⁻¹) ^ N * (seriesFrom cs k y - seriesFrom cs k (y + 1)) =
        eval (diffSum cs k N) y⁻¹ := by
  induction cs with
  | nil => intro k _; simp [seriesFrom, diffSum]
  | cons c cs ih =>
    intro k hk
    simp only [List.length_cons] at hk
    have hrec := ih (k + 1) (by omega)
    have hsplit : ∀ w : ℝ, seriesFrom (c :: cs) k w =
        c * w⁻¹ ^ (2 * k + 1) + seriesFrom cs (k + 1) w := by
      intro w
      rw [seriesFrom, seriesFrom, eval_cons]
      ring
    rw [diffSum, eval_addP, eval_scaleP, eval_diffTerm, hsplit, hsplit, ← hrec]
    obtain ⟨j, rfl⟩ : ∃ j, N = j + (2 * k + 1) := ⟨N - (2 * k + 1), by omega⟩
    rw [show j + (2 * k + 1) - 2 * k - 1 = j by omega]
    have hy0 : y ≠ 0 := hy.ne'
    have h1 : (1 + y⁻¹) ≠ 0 := by positivity
    have hz : (y + 1)⁻¹ = y⁻¹ / (1 + y⁻¹) := by
      rw [div_eq_mul_inv, ← mul_inv, mul_add, mul_one, mul_inv_cancel₀ hy0]
    have hkey : (1 + y⁻¹) ^ (j + (2 * k + 1)) * (y⁻¹ ^ (2 * k + 1) / (1 + y⁻¹) ^ (2 * k + 1)) =
        (1 + y⁻¹) ^ j * y⁻¹ ^ (2 * k + 1) := by
      rw [pow_add (1 + y⁻¹) j (2 * k + 1), mul_assoc, mul_div_assoc',
        mul_div_cancel_left₀ _ (pow_ne_zero _ h1)]
    rw [hz, div_pow]
    linear_combination (-(c : ℝ)) * hkey

theorem series_eq (cs : List ℚ) (y : ℝ) : series cs y = seriesFrom cs 0 y := by
  rw [series, seriesFrom, mul_zero, zero_add, pow_one]

theorem rho_identity (cs : List ℚ) (hcs : 0 < cs.length) {y : ℝ} (hy : 0 < y) :
    (1 + y⁻¹) ^ (2 * cs.length - 1) * rho cs y =
      eval (qpoly cs) y⁻¹ + (1 + y⁻¹) ^ (2 * cs.length - 1) * (y + 1 / 2) *
        (log (1 + y⁻¹) - y⁻¹ * eval (log1pQuotCoeffs (2 * cs.length + 3)) y⁻¹) := by
  have hdiff := diffSum_eval cs (2 * cs.length - 1) hy 0 (by omega)
  rw [← series_eq, ← series_eq] at hdiff
  have hyz : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  rw [qpoly, eval_subP, eval_mulP, eval_powP, eval_addP, eval_mulP, eval_one_one, rho, phi,
    one_div y]
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
  linear_combination ((1 + y⁻¹) ^ (2 * cs.length - 1) *
    eval (log1pQuotCoeffs (2 * cs.length + 3)) y⁻¹) * hyz - hdiff

theorem eval_of_take (p : List ℚ) (k : ℕ) (h : p.take k = List.replicate k 0) (x : ℝ) :
    eval p x = x ^ k * eval (p.drop k) x := by
  conv_lhs => rw [← List.take_append_drop k p, h]
  exact eval_replicate_append k _ x

theorem abs_rho_le (cs : List ℚ) (hcs : 0 < cs.length) (z0 M : ℚ) (d : ℕ) (hz0 : 0 < z0)
    (hz1 : z0 < 1)
    (hzero : (qpoly cs).take (2 * cs.length + 2) = List.replicate (2 * cs.length + 2) 0)
    (hb : check ((qpoly cs).drop (2 * cs.length + 2)) 0 z0 M d = true)
    {y : ℝ} (hy : 1 / (z0 : ℝ) ≤ y) :
    |rho cs y| ≤ ((M : ℝ) + z0 * (1 + z0 / 2) / (1 - z0)) * y⁻¹ ^ (2 * cs.length + 2) := by
  have hz0r : (0 : ℝ) < z0 := by exact_mod_cast hz0
  have hz1r : (z0 : ℝ) < 1 := by exact_mod_cast hz1
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  set z := y⁻¹ with hzdef
  have hz : 0 < z := inv_pos.mpr hypos
  have hzle : z ≤ z0 := by
    rw [hzdef, inv_le_comm₀ hypos hz0r]
    rwa [one_div] at hy
  have hyz : y * z = 1 := mul_inv_cancel₀ hypos.ne'
  set m := cs.length with hm
  set V := (1 + z) ^ (2 * m - 1) with hV
  have hV1 : 1 ≤ V := one_le_pow₀ (by linarith)
  set E := log (1 + z) - z * eval (log1pQuotCoeffs (2 * m + 3)) z with hE
  have hid := rho_identity cs hcs hypos
  rw [← hzdef, ← hm, ← hV, ← hE] at hid
  have hA : |eval (qpoly cs) z| ≤ z ^ (2 * m + 2) * M := by
    rw [eval_of_take _ _ hzero, abs_mul, abs_of_pos (pow_pos hz (2 * m + 2))]
    exact mul_le_mul_of_nonneg_left
      (check_sound _ 0 z0 M d hb z (by push_cast; exact hz.le) hzle) (by positivity)
  have hEb : |E| ≤ z ^ (2 * m + 4) / (1 - z) := by
    have h := log1p_remainder z (by rw [abs_of_pos hz]; linarith) (2 * m + 3)
    rw [eval_log1pCoeffs, abs_of_pos hz, show 2 * m + 3 + 1 = 2 * m + 4 by ring] at h
    exact h
  have hV0 : V ≠ 0 := (by linarith : (0 : ℝ) < V).ne'
  have hrho : rho cs y = eval (qpoly cs) z / V + (y + 1 / 2) * E := by
    rw [div_add' _ _ _ hV0, eq_div_iff hV0]
    linear_combination hid
  have hyh : 0 < y + 1 / 2 := by linarith
  have hfirst : |eval (qpoly cs) z / V| ≤ z ^ (2 * m + 2) * M := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < V)]
    exact (div_le_self (abs_nonneg _) hV1).trans hA
  have hsecond : |(y + 1 / 2) * E| ≤ z ^ (2 * m + 2) * (z0 * (1 + z0 / 2) / (1 - z0)) := by
    rw [abs_mul, abs_of_pos hyh]
    have hy2 : (y + 1 / 2) * z ^ (2 * m + 4) = z ^ (2 * m + 2) * (z * (1 + z / 2)) := by
      have : (y + 1 / 2) * z ^ (2 * m + 4) =
          (y * z) * z ^ (2 * m + 3) + z ^ (2 * m + 4) / 2 := by ring
      rw [this, hyz]
      ring
    have hq : z * (1 + z / 2) / (1 - z) ≤ z0 * (1 + z0 / 2) / (1 - z0) := by
      apply div_le_div₀ (by positivity) (by nlinarith) (by linarith) (by linarith)
    calc (y + 1 / 2) * |E| ≤ (y + 1 / 2) * (z ^ (2 * m + 4) / (1 - z)) :=
          mul_le_mul_of_nonneg_left hEb hyh.le
      _ = z ^ (2 * m + 2) * (z * (1 + z / 2) / (1 - z)) := by
          rw [mul_div_assoc', hy2, mul_div_assoc]
      _ ≤ z ^ (2 * m + 2) * (z0 * (1 + z0 / 2) / (1 - z0)) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
  rw [hrho]
  calc |eval (qpoly cs) z / V + (y + 1 / 2) * E|
      ≤ |eval (qpoly cs) z / V| + |(y + 1 / 2) * E| := abs_add_le _ _
    _ ≤ z ^ (2 * m + 2) * M + z ^ (2 * m + 2) * (z0 * (1 + z0 / 2) / (1 - z0)) :=
        add_le_add hfirst hsecond
    _ = ((M : ℝ) + z0 * (1 + z0 / 2) / (1 - z0)) * z ^ (2 * m + 2) := by ring

theorem pow_succ_le (a : ℝ) (ha : 0 ≤ a) (p : ℕ) : (a + 1 + p) * a ^ p ≤ (a + 1) ^ (p + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hap : 0 ≤ a ^ p := pow_nonneg ha p
    calc (a + 1 + ((p + 1 : ℕ) : ℝ)) * a ^ (p + 1) = (a + 2 + p) * a * a ^ p := by
          push_cast
          ring
      _ ≤ (a + 1) * (a + 1 + p) * a ^ p := by
          apply mul_le_mul_of_nonneg_right _ hap
          have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
          nlinarith
      _ ≤ (a + 1) * (a + 1) ^ (p + 1) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (a + 1) ^ (p + 1 + 1) := by ring

/-- `1 / (p (y - 1) ^ p)`, whose differences bound `y ^ -(p + 1)`. -/
noncomputable def tele (p : ℕ) (y : ℝ) : ℝ := 1 / ((p : ℝ) * (y - 1) ^ p)

theorem inv_pow_le_telescope {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : 0 < p) :
    y⁻¹ ^ (p + 1) ≤ tele p y - tele p (y + 1) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have ha : 0 < y - 1 := by linarith
  have hA : 0 < (y - 1) ^ p := pow_pos ha p
  have hY : 0 < y ^ p := pow_pos (by linarith) p
  have key := pow_succ_le (y - 1) ha.le p
  rw [show y - 1 + 1 = y by ring, pow_succ] at key
  rw [tele, tele, show y + 1 - 1 = y by ring, inv_pow, ← one_div, pow_succ,
    div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (le_of_lt (mul_pos hpr hY))]

theorem continuous_eval (p : List ℚ) : Continuous (eval p) := by
  induction p with
  | nil => exact continuous_const
  | cons a p ih =>
    have : eval (a :: p) = fun x => (a : ℝ) + x * eval p x := by
      funext x
      rfl
    rw [this]
    exact continuous_const.add (continuous_id.mul ih)

theorem tendsto_R (cs : List ℚ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => R cs (x + n)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (x + n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hg
  have hser : Tendsto (fun n : ℕ => series cs (x + n)) atTop (𝓝 (0 * eval cs (0 ^ 2))) :=
    hinv.mul (((continuous_eval cs).tendsto _).comp (hinv.pow 2))
  rw [zero_mul] at hser
  have h := (tendsto_F hx).sub hser
  rw [sub_zero] at h
  exact h

theorem R_sub_succ (cs : List ℚ) {x : ℝ} (hx : 0 < x) : R cs x - R cs (x + 1) = rho cs x := by
  rw [R, R, rho, ← F_sub_succ hx]
  ring

theorem R_telescope (cs : List ℚ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    R cs x - R cs (x + n) = ∑ k ∈ range n, rho cs (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    rw [sum_range_succ, ← ih, ← R_sub_succ cs hxn, Nat.cast_succ, add_assoc]
    ring

theorem abs_remainder_le (cs : List ℚ) (hcs : 0 < cs.length) (z0 M : ℚ) (d : ℕ) (hz0 : 0 < z0)
    (hz1 : z0 < 1)
    (hzero : (qpoly cs).take (2 * cs.length + 2) = List.replicate (2 * cs.length + 2) 0)
    (hb : check ((qpoly cs).drop (2 * cs.length + 2)) 0 z0 M d = true)
    {x : ℝ} (hx : 1 / (z0 : ℝ) ≤ x) :
    |lgamma x - lead x - series cs x| ≤ ((M : ℝ) + z0 * (1 + z0 / 2) / (1 - z0)) /
      ((2 * cs.length + 1) * (x - 1) ^ (2 * cs.length + 1)) := by
  have hz0r : (0 : ℝ) < z0 := by exact_mod_cast hz0
  have hz1r : (z0 : ℝ) < 1 := by exact_mod_cast hz1
  have hx1 : 1 < x := lt_of_lt_of_le (by rw [lt_div_iff₀ hz0r]; linarith) hx
  have hx0 : 0 < x := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (M : ℝ) + z0 * (1 + z0 / 2) / (1 - z0) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = 2 * cs.length + 1 := ⟨_, rfl⟩
  rw [← hK, show (2 * (cs.length : ℝ) + 1) = (p : ℝ) by rw [hp]; norm_cast, ← hp]
  have hrho : ∀ y : ℝ, 1 / (z0 : ℝ) ≤ y → |rho cs y| ≤ K * y⁻¹ ^ (p + 1) := by
    intro y hy
    have h := abs_rho_le cs hcs z0 M d hz0 hz1 hzero hb hy
    rwa [← hK, show 2 * cs.length + 2 = p + 1 by omega] at h
  have hK0 : 0 ≤ K := by
    have h := hrho x hx
    have hpow : 0 < x⁻¹ ^ (p + 1) := by positivity
    by_contra hneg
    have : K * x⁻¹ ^ (p + 1) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpow
    linarith [abs_nonneg (rho cs x)]
  have hstep : ∀ k : ℕ, |rho cs (x + k)| ≤ K * (tele p (x + k) - tele p (x + k + 1)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact (hrho (x + k) (by linarith)).trans (mul_le_mul_of_nonneg_left
      (inv_pow_le_telescope (by linarith) (by omega)) hK0)
  have hbound : ∀ n : ℕ, |R cs x - R cs (x + n)| ≤ K * tele p x := by
    intro n
    rw [R_telescope cs hx0 n]
    have hsum : ∑ k ∈ range n, K * (tele p (x + k) - tele p (x + k + 1)) =
        K * (tele p x - tele p (x + n)) := by
      rw [← mul_sum]
      congr 1
      have := sum_range_sub' (fun k : ℕ => tele p (x + k)) n
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at this
      rw [← this]
      refine sum_congr rfl fun k _ => ?_
      rw [add_assoc]
    have hTn : 0 ≤ tele p (x + n) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : 0 < x + n - 1 := by linarith
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (pow_nonneg this.le p))
    calc |∑ k ∈ range n, rho cs (x + k)| ≤ ∑ k ∈ range n, |rho cs (x + k)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range n, K * (tele p (x + k) - tele p (x + k + 1)) :=
          sum_le_sum fun k _ => hstep k
      _ = K * (tele p x - tele p (x + n)) := hsum
      _ ≤ K * tele p x := by nlinarith [mul_nonneg hK0 hTn]
  have hlim : Tendsto (fun n : ℕ => |R cs x - R cs (x + n)|) atTop (𝓝 |R cs x - 0|) :=
    ((tendsto_const_nhds).sub (tendsto_R cs hx0)).abs
  rw [sub_zero] at hlim
  have hR := le_of_tendsto' hlim hbound
  have hRdef : R cs x = lgamma x - lead x - series cs x := by rw [R, F]
  rw [← hRdef]
  calc |R cs x| ≤ K * tele p x := hR
    _ = K / ((p : ℝ) * (x - 1) ^ p) := by rw [tele, mul_one_div]

/-- `B (2 k)/(2 k (2 k - 1))` for `k` from 1 to 12. -/
def stirCoeffs : List ℚ :=
  [1 / 12, -1 / 360, 1 / 1260, -1 / 1680, 1 / 1188, -691 / 360360, 1 / 156, -3617 / 122400,
    43867 / 244188, -174611 / 125400, 77683 / 5796, -236364091 / 1506960]

theorem stirCoeffs_zero :
    (qpoly stirCoeffs).take (2 * stirCoeffs.length + 2) =
      List.replicate (2 * stirCoeffs.length + 2) 0 := by
  decide +kernel

theorem stirCoeffs_check :
    check ((qpoly stirCoeffs).drop (2 * stirCoeffs.length + 2)) 0 (1 / 16) 104000 0 = true := by
  decide +kernel

/-- Stirling's series with twelve terms: for `x ≥ 16` the remainder lies below
`104001 / (25 (x - 1) ^ 25)`, which is below `2 ^ -85` at 16. -/
theorem stirling_twelve {x : ℝ} (hx : 16 ≤ x) :
    |lgamma x - lead x - series stirCoeffs x| ≤ 104001 / (25 * (x - 1) ^ 25) := by
  have h := abs_remainder_le stirCoeffs (by decide) (1 / 16) 104000 0 (by norm_num) (by norm_num)
    stirCoeffs_zero stirCoeffs_check (x := x) (by norm_num; linarith)
  have hlen : stirCoeffs.length = 12 := rfl
  rw [hlen] at h
  have hx1 : 0 < x - 1 := by linarith
  have hnum : ((104000 : ℚ) : ℝ) + ((1 / 16 : ℚ) : ℝ) * (1 + ((1 / 16 : ℚ) : ℝ) / 2) /
      (1 - ((1 / 16 : ℚ) : ℝ)) ≤ 104001 := by norm_num
  have hden : (2 * ((12 : ℕ) : ℝ) + 1) * (x - 1) ^ (2 * 12 + 1) = 25 * (x - 1) ^ 25 := by
    norm_num
  rw [hden] at h
  exact h.trans (div_le_div_of_nonneg_right hnum
    (mul_nonneg (by norm_num) (pow_nonneg hx1.le 25)))

#print axioms F_sub_succ
#print axioms tendsto_F
#print axioms rho_identity
#print axioms abs_rho_le
#print axioms abs_remainder_le
#print axioms stirling_twelve

end LeanExe.ProofKit.GammaStirling
