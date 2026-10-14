import LeanExe.ProofKit.GammaBasic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Slope

/-!
Convexity of `lgamma = log |Γ|` and its consequences for the facts next to the zeros of `lgamma`.
`lgamma` is convex on `(0, ∞)` (Mathlib's `Real.convexOn_log_Gamma`), so the divided difference
`(lgamma (x0 + s) - lgamma x0)/s` increases with `s` (`dd_mono`), and between `-τ` and `τ` it lies
within the bounds at `±τ` plus the variation of a polynomial (`dd_center`).  On each interval
`(-n - 1, -n)`, `lgamma x = lgamma (x + n + 1) - Σ k ≤ n, log (-(x + k))` is a sum of convex
functions (`convexOn_lgamma_neg`), so a convex function's values at four points bound it on the
whole interval: from above between two points where it is negative (`convex_mid`), and from below
outside a point where it is positive next to one where it is negative (`convex_left`,
`convex_right`).
-/

namespace LeanExe.ProofKit.GammaConvex

open Real Set Finset GammaBasic

/-- `lgamma` is convex on `(0, ∞)`. -/
theorem convexOn_lgamma : ConvexOn ℝ (Ioi 0) lgamma :=
  Real.convexOn_log_Gamma.congr fun _ _ => rfl

/-- The divided difference of `lgamma` at a positive point increases. -/
theorem dd_mono {x0 s1 s2 : ℝ} (hx0 : 0 < x0) (h1 : 0 < x0 + s1) (h2 : 0 < x0 + s2)
    (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) (h : s1 ≤ s2) :
    (lgamma (x0 + s1) - lgamma x0) / s1 ≤ (lgamma (x0 + s2) - lgamma x0) / s2 := by
  have hm := convexOn_lgamma.secant_mono (a := x0) (x := x0 + s1) (y := x0 + s2) (mem_Ioi.mpr hx0)
    (mem_Ioi.mpr h1) (mem_Ioi.mpr h2) (by intro he; apply hs1; linarith)
    (by intro he; apply hs2; linarith) (by linarith)
  simpa only [add_sub_cancel_left] using hm

/-- The divided difference within `ε + 2 V` of `P` on `[-τ, τ]`, from its values at `±τ` and the
variation `V` of `P`. -/
theorem dd_center {x0 τ ε V : ℝ} (hx0 : 0 < x0) (hτ : 0 < τ) (hτx : τ < x0) (P : ℝ → ℝ)
    (hP : ∀ s, |s| ≤ τ → |P s - P 0| ≤ V)
    (hp : |(lgamma (x0 + τ) - lgamma x0) / τ - P τ| ≤ ε)
    (hm : |(lgamma (x0 + -τ) - lgamma x0) / -τ - P (-τ)| ≤ ε)
    {s : ℝ} (hs0 : s ≠ 0) (hs : |s| ≤ τ) :
    |(lgamma (x0 + s) - lgamma x0) / s - P s| ≤ ε + 2 * V := by
  have hsl := abs_le.mp hs
  have g1 := dd_mono (s1 := -τ) (s2 := s) hx0 (by linarith) (by linarith)
    (neg_ne_zero.mpr hτ.ne') hs0 hsl.1
  have g2 := dd_mono (s1 := s) (s2 := τ) hx0 (by linarith) (by linarith) hs0 hτ.ne' hsl.2
  have p1 := abs_le.mp (hP s hs)
  have p2 := abs_le.mp (hP τ (by rw [abs_of_pos hτ]))
  have p3 := abs_le.mp (hP (-τ) (by rw [abs_neg, abs_of_pos hτ]))
  have q1 := abs_le.mp hp
  have q2 := abs_le.mp hm
  rw [abs_le]
  constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, q1.1, q1.2, q2.1, q2.2]

/-- `x ↦ lgamma (x + c)` is convex where `x + c > 0`. -/
theorem convexOn_shift {s : Set ℝ} {c : ℝ} (hs : Convex ℝ s) (h : ∀ x ∈ s, 0 < x + c) :
    ConvexOn ℝ s (fun x => lgamma (x + c)) := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  have hc := convexOn_lgamma.2 (mem_Ioi.mpr (h x hx)) (mem_Ioi.mpr (h y hy)) ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have e : a * x + b * y + c = a * (x + c) + b * (y + c) := by linear_combination (-c) * hab
  rw [e]
  exact hc

/-- `x ↦ -log (c - x)` is convex where `c - x > 0`. -/
theorem convexOn_neg_log {s : Set ℝ} {c : ℝ} (hs : Convex ℝ s) (h : ∀ x ∈ s, 0 < c - x) :
    ConvexOn ℝ s (fun x => -log (c - x)) := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.mpr (h x hx)) (mem_Ioi.mpr (h y hy))
    ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have e : c - (a * x + b * y) = a * (c - x) + b * (c - y) := by linear_combination (-c) * hab
  rw [e]
  linarith

/-- A finite sum of convex functions is convex. -/
theorem convexOn_sum_range {s : Set ℝ} (hs : Convex ℝ s) {g : ℕ → ℝ → ℝ} (m : ℕ)
    (h : ∀ k < m, ConvexOn ℝ s (g k)) : ConvexOn ℝ s (fun x => ∑ k ∈ range m, g k x) := by
  induction m with
  | zero => simpa using convexOn_const (0 : ℝ) hs
  | succ m ih =>
    have hm := (ih fun k hk => h k (by omega)).add (h m (by omega))
    refine hm.congr fun x _ => ?_
    simp [Finset.sum_range_succ]

theorem add_nat_ne_zero {x : ℝ} (h : NotPole x) (k : ℕ) : x + k ≠ 0 :=
  fun h0 => h k (by linarith)

/-- `lgamma x = lgamma (x + m) - Σ k < m, log (x + k)` away from the poles. -/
theorem lgamma_eq_shift {x : ℝ} (h : NotPole x) (m : ℕ) :
    lgamma x = lgamma (x + m) - ∑ k ∈ range m, log (x + k) := by
  have hg := gamma_add_nat h m
  rw [lgamma, lgamma, hg, Real.log_mul (Gamma_ne_zero h) (shift_prod_ne_zero h m),
    Real.log_prod (fun k _ => add_nat_ne_zero h k)]
  ring

/-- `lgamma` is convex on each interval `(-n - 1, -n)`. -/
theorem convexOn_lgamma_neg (n : ℕ) : ConvexOn ℝ (Ioo (-(n : ℝ) - 1) (-n)) lgamma := by
  have hs : Convex ℝ (Ioo (-(n : ℝ) - 1) (-n)) := convex_Ioo _ _
  have h1 : ConvexOn ℝ (Ioo (-(n : ℝ) - 1) (-n)) (fun x => lgamma (x + ((n + 1 : ℕ) : ℝ))) :=
    convexOn_shift hs fun x hx => by
      have := hx.1
      push_cast
      linarith
  have h2 : ConvexOn ℝ (Ioo (-(n : ℝ) - 1) (-n))
      (fun x => ∑ k ∈ range (n + 1), -log (-(k : ℝ) - x)) :=
    convexOn_sum_range hs (n + 1) fun k hk => convexOn_neg_log hs fun x hx => by
      have := hx.2
      have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hk
      linarith
  refine (h1.add h2).congr fun x hx => ?_
  have hnp : NotPole x := by
    intro m hm
    have h3 := hx.1
    have h4 := hx.2
    rw [hm] at h3 h4
    have h5 : m < n + 1 := by
      have : (m : ℝ) < n + 1 := by linarith
      exact_mod_cast this
    have h6 : n < m := by
      have : (n : ℝ) < m := by linarith
      exact_mod_cast this
    omega
  rw [lgamma_eq_shift hnp (n + 1)]
  simp only [Pi.add_apply, Finset.sum_neg_distrib]
  have hlog : ∀ k ∈ range (n + 1), log (-(k : ℝ) - x) = log (x + k) := by
    intro k _
    rw [show -(k : ℝ) - x = -(x + k) by ring, Real.log_neg_eq_log]
  rw [Finset.sum_congr rfl hlog]
  ring

/-- A convex function at a point left of `xa`, where it is nonnegative, next to `xb`, where it is
not positive, is at least its value at `xa`. -/
theorem convex_left {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x xa xb : ℝ} (hx : x ∈ s)
    (hb : xb ∈ s) (h1 : x ≤ xa) (h2 : xa < xb) (hfa : 0 ≤ f xa) (hfb : f xb ≤ 0) :
    f xa ≤ f x := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]
  have hd : 0 < xb - x := by linarith
  set l := (xb - xa) / (xb - x) with hl
  have hl0 : 0 < l := div_pos (by linarith) hd
  have hl1 : l ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hc := hf.2 hx hb hl0.le (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
  simp only [smul_eq_mul] at hc
  have hlx : l * (xb - x) = xb - xa := by rw [hl]; exact div_mul_cancel₀ _ hd.ne'
  have e : l * x + (1 - l) * xb = xa := by linear_combination -hlx
  rw [e] at hc
  have hp := mul_nonneg (sub_nonneg.mpr hl1) (neg_nonneg.mpr hfb)
  have hfx : 0 ≤ f x := by
    rcases le_or_gt 0 (f x) with h0 | hneg
    · exact h0
    · nlinarith [mul_pos hl0 (neg_pos.mpr hneg)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hl1) hfx]

/-- The mirror image of `convex_left`. -/
theorem convex_right {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x xc xd : ℝ} (hx : x ∈ s)
    (hc : xc ∈ s) (h1 : xd ≤ x) (h2 : xc < xd) (hfd : 0 ≤ f xd) (hfc : f xc ≤ 0) :
    f xd ≤ f x := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]
  have hd : 0 < x - xc := by linarith
  set l := (xd - xc) / (x - xc) with hl
  have hl0 : 0 < l := div_pos (by linarith) hd
  have hl1 : l ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hcv := hf.2 hx hc hl0.le (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
  simp only [smul_eq_mul] at hcv
  have hlx : l * (x - xc) = xd - xc := by rw [hl]; exact div_mul_cancel₀ _ hd.ne'
  have e : l * x + (1 - l) * xc = xd := by linear_combination hlx
  rw [e] at hcv
  have hp := mul_nonneg (sub_nonneg.mpr hl1) (neg_nonneg.mpr hfc)
  have hfx : 0 ≤ f x := by
    rcases le_or_gt 0 (f x) with h0 | hneg
    · exact h0
    · nlinarith [mul_pos hl0 (neg_pos.mpr hneg)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hl1) hfx]

/-- A convex function between two points lies below the larger of its values there. -/
theorem convex_mid {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x xb xc : ℝ} (hb : xb ∈ s)
    (hc : xc ∈ s) (h1 : xb ≤ x) (h2 : x ≤ xc) : f x ≤ max (f xb) (f xc) :=
  hf.le_on_segment hb hc (by rw [segment_eq_Icc (h1.trans h2)]; exact ⟨h1, h2⟩)

#print axioms dd_mono
#print axioms dd_center
#print axioms convexOn_lgamma_neg
#print axioms convex_left
#print axioms convex_right
#print axioms convex_mid

end LeanExe.ProofKit.GammaConvex
