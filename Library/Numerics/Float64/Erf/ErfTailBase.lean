import LeanExe.ProofKit.RealErfScaled
import LeanExe.ProofKit.PolyCalculus
import Library.Numerics.Float64.Erf.ErfKernelSmall

/-!
General lemmas for the tail kernels of `s_erf.c`.  On `[1.25, 28)` the code computes
`erfc x = exp (-x² - 0.5625 + R (s)/S (s))/x` with `s = 1/x²`, so the rational function models
`log (x erfcx x) + 0.5625`, and `tailF R S x = R (s)/S (s) - 9/16 - log (x erfcx x)` is its error.

The proof works on pieces `[a, b]` of the range.  On each piece a polynomial `p` in `t = x - c`
models `erfcxN x`: `defectP p c` is `p' - 2 x p + 1`, which `piece_model` turns, with a bound at
`b`, into a bound on `|erfcxN - p|` by `ode_backward`.  The derivative of `tailF` is a quotient of
polynomials in `x` minus `1/x + 2x - 1/erfcxN`, and `checkN`, `checkW` give a polynomial check that
bounds the derivative with `p` in place of `erfcxN` (`deriv_bound`).  `anchor_bound` bounds `tailF` at
a rational point from rational enclosures of the exponential of the model, of `2/√π`, and of
`erfcxN`, and `combine` adds the derivative bound over a stretch of the piece.
-/

namespace Library.Numerics.Float64.Erf.ErfTailBase
open Real Set Filter Topology LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErf
  RealErfScaled ErfKernelSmall

/-- The kernel's model `R (s)/S (s) - 9/16` with `s = 1/x²`. -/
noncomputable def tailW (R S : List ℚ) (x : ℝ) : ℝ := eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹ - 9 / 16

/-- The model's error: `tailW R S x - log (x erfcx x)`. -/
noncomputable def tailF (R S : List ℚ) (x : ℝ) : ℝ := tailW R S x - Real.log (x * erfcx x)

/-! ### Rational evaluation -/

/-- `eval` over `ℚ`. -/
def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

theorem eval_cast (p : List ℚ) (x : ℚ) : eval p (x : ℝ) = ((evalQ p x : ℚ) : ℝ) := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [evalQ, ih]

/-! ### The model's derivative -/

/-- `x ^ k`. -/
def xpow (k : ℕ) : List ℚ := powP [0, 1] k

theorem eval_xpow (k : ℕ) (x : ℝ) : eval (xpow k) x = x ^ k := by
  rw [xpow, eval_powP]
  simp

/-- The numerator of the derivative of `x ^ k Rh / Sh`. -/
def numP (Rh Sh : List ℚ) (k : ℕ) : List ℚ :=
  subP (mulP (addP (mulP (derivP (xpow k)) Rh) (mulP (xpow k) (derivP Rh))) Sh)
    (mulP (mulP (xpow k) Rh) (derivP Sh))

theorem tailW_eq (R S : List ℚ) (m n : ℕ) (hR : R.length ≤ m + 1) (hS : S.length ≤ n + 1)
    (hmn : m ≤ n) {x : ℝ} (hx : x ≠ 0) :
    tailW R S x = eval (xpow (2 * (n - m))) x * eval (hatP R m) x / eval (hatP S n) x - 9 / 16 := by
  rw [tailW, eval_hatP R m hR x hx, eval_hatP S n hS x hx, eval_xpow]
  have h : x ^ (2 * (n - m)) * x ^ (2 * m) = x ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have hxn : x ^ (2 * n) ≠ 0 := pow_ne_zero _ hx
  congr 1
  rw [← mul_assoc, h, mul_div_mul_left _ _ hxn]

theorem hasDerivAt_tailW (R S : List ℚ) (m n : ℕ) (hR : R.length ≤ m + 1)
    (hS : S.length ≤ n + 1) (hmn : m ≤ n) {x : ℝ} (hx : 0 < x)
    (hSx : eval (hatP S n) x ≠ 0) :
    HasDerivAt (tailW R S)
      (eval (numP (hatP R m) (hatP S n) (2 * (n - m))) x / eval (hatP S n) x ^ 2) x := by
  set X := xpow (2 * (n - m))
  set Rh := hatP R m
  set Sh := hatP S n
  have hc := (hasDerivAt_eval X x).mul (hasDerivAt_eval Rh x)
  have hq := hc.div (hasDerivAt_eval Sh x) hSx
  have hv := hq.sub_const (9 / 16 : ℝ)
  have he : (fun y => eval X y * eval Rh y / eval Sh y - 9 / 16) =ᶠ[𝓝 x] tailW R S := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (tailW_eq R S m n hR hS hmn (ne_of_gt hy)).symm
  refine (hv.congr_of_eventuallyEq he.symm).congr_deriv ?_
  simp only [numP, eval_subP, eval_mulP, eval_addP, Pi.mul_apply]
  rfl

theorem hasDerivAt_logx (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => Real.log (y * erfcx y)) (1 / x + 2 * x - 1 / erfcxN x) x := by
  have hpos : x * erfcx x ≠ 0 := (mul_pos hx (erfcx_pos x)).ne'
  have h := ((hasDerivAt_id x).mul (hasDerivAt_erfcx x)).log hpos
  refine h.congr_deriv ?_
  have hE := erfcx_eq x
  have hs : scale ≠ 0 := scale_pos.ne'
  have hF : erfcxN x ≠ 0 := (erfcxN_pos x).ne'
  have hx0 : x ≠ 0 := hx.ne'
  simp only [Pi.mul_apply, id]
  rw [hE]
  field_simp
  ring

theorem hasDerivAt_tailF (R S : List ℚ) (m n : ℕ) (hR : R.length ≤ m + 1)
    (hS : S.length ≤ n + 1) (hmn : m ≤ n) {x : ℝ} (hx : 0 < x)
    (hSx : eval (hatP S n) x ≠ 0) :
    HasDerivAt (tailF R S)
      (eval (numP (hatP R m) (hatP S n) (2 * (n - m))) x / eval (hatP S n) x ^ 2 -
        (1 / x + 2 * x - 1 / erfcxN x)) x :=
  (hasDerivAt_tailW R S m n hR hS hmn hx hSx).sub (hasDerivAt_logx x hx)

/-! ### The checks of one piece -/

/-- `c + t`. -/
def linP (c : ℚ) : List ℚ := [c, 1]

theorem eval_linP (c : ℚ) (t : ℝ) : eval (linP c) t = c + t := by simp [linP]

/-- `p' - 2 (c + t) p + 1`, the defect of the model `p` in the equation of `erfcxN`. -/
def defectP (p : List ℚ) (c : ℚ) : List ℚ := addP (subP (derivP p) (mulP [2 * c, 2] p)) [1]

theorem eval_defectP (p : List ℚ) (c : ℚ) (t : ℝ) :
    eval (defectP p c) t = eval (derivP p) t - 2 * (c + t) * eval p t + 1 := by
  simp only [defectP, eval_addP, eval_subP, eval_mulP, eval_cons, eval_nil]
  push_cast
  ring

/-- `NUM (c + t) (c + t) p (t) - Sh (c + t)² (p + 2 (c + t)² p - (c + t))`. -/
def checkN (NUM Sh p : List ℚ) (c : ℚ) : List ℚ :=
  subP (mulP (shift c NUM) (mulP (linP c) p))
    (mulP (mulP (shift c Sh) (shift c Sh))
      (subP (addP p (mulP (scaleP 2 (mulP (linP c) (linP c))) p)) (linP c)))

/-- `Sh (c + t)² (c + t) p (t)`. -/
def checkW (Sh p : List ℚ) (c : ℚ) : List ℚ := mulP (mulP (shift c Sh) (shift c Sh)) (mulP (linP c) p)

theorem eval_checkN (NUM Sh p : List ℚ) (c : ℚ) (x : ℝ) :
    eval (checkN NUM Sh p c) (x - c) = eval NUM x * x * eval p (x - c) -
      eval Sh x ^ 2 * (eval p (x - c) + 2 * x ^ 2 * eval p (x - c) - x) := by
  simp only [checkN, eval_subP, eval_mulP, eval_addP, eval_scaleP, eval_shift, eval_linP,
    add_sub_cancel]
  push_cast
  ring

theorem eval_checkW (Sh p : List ℚ) (c : ℚ) (x : ℝ) :
    eval (checkW Sh p c) (x - c) = eval Sh x ^ 2 * x * eval p (x - c) := by
  simp only [checkW, eval_mulP, eval_shift, eval_linP, add_sub_cancel]
  ring

/-! ### The lemmas of one piece -/

/-- The model `p` stays within `σ + η (b - x)` of `erfcxN` on `[a, b]`. -/
theorem piece_model (p : List ℚ) (a b c η σ : ℚ) (ha : (0 : ℝ) ≤ a)
    (hd : Bounded (defectP p c) (a - c) (b - c) η)
    (hb : |erfcxN b - eval p ((b : ℝ) - c)| ≤ σ) {x : ℝ} (hx : x ∈ Icc (a : ℝ) b) :
    |erfcxN x - eval p (x - c)| ≤ (σ : ℝ) + η * ((b : ℝ) - x) := by
  refine erfcxN_backward (fun y => eval p (y - c)) (fun y => eval (derivP p) (y - c)) ha
    (fun y _ => hasDerivAt_eval_sub p c y) ?_ hb hx
  intro y hy
  have h := hd (y - c) (by push_cast; linarith [hy.1]) (by push_cast; linarith [hy.2])
  rw [eval_defectP] at h
  have he : (c : ℝ) + (y - c) = y := by ring
  rw [he] at h
  exact h

/-- On `[a, b]`, the derivative of `tailF` is at most `η + σ/(pmin (pmin - σ))` in magnitude, from
the derivative check against the model `p`, a lower bound `pmin` on `p`, and the model's
accuracy `σ`. -/
theorem deriv_bound (R S : List ℚ) (m n : ℕ) (p : List ℚ) (a b c η M N pmin σ : ℚ) (ha : (0 : ℝ) < a)
    (hu : Bounded (addP (subP (checkN (numP (hatP R m) (hatP S n) (2 * (n - m))) (hatP S n) p c)
      (scaleP η (checkW (hatP S n) p c))) [M]) (a - c) (b - c) M)
    (hl : Bounded (subP (addP (checkN (numP (hatP R m) (hatP S n) (2 * (n - m))) (hatP S n) p c)
      (scaleP η (checkW (hatP S n) p c))) [N]) (a - c) (b - c) N)
    (hSpos : ∀ x ∈ Icc (a : ℝ) b, 0 < eval (hatP S n) x)
    (hp : ∀ x ∈ Icc (a : ℝ) b, (pmin : ℝ) ≤ eval p (x - c))
    (hσ : ∀ x ∈ Icc (a : ℝ) b, |erfcxN x - eval p (x - c)| ≤ σ) (hσp : (σ : ℝ) < pmin)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) b) :
    |eval (numP (hatP R m) (hatP S n) (2 * (n - m))) x / eval (hatP S n) x ^ 2 -
        (1 / x + 2 * x - 1 / erfcxN x)| ≤ (η : ℝ) + (σ : ℝ) / (pmin * (pmin - σ)) := by
  set NUM := numP (hatP R m) (hatP S n) (2 * (n - m))
  set Sh := hatP S n
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hS0 := hSpos x hx
  have hpx := hp x hx
  have hσx := hσ x hx
  have hσ0 : (0 : ℝ) ≤ σ := (abs_nonneg _).trans hσx
  have hpmin : (0 : ℝ) < pmin := lt_of_le_of_lt hσ0 hσp
  set P := eval p (x - c)
  have hP : 0 < P := lt_of_lt_of_le hpmin hpx
  have hw := abs_le_weighted _ _ η (a - c) (b - c) M N hu hl (x - c)
    (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
  rw [eval_checkN, eval_checkW] at hw
  have hW : 0 < eval Sh x ^ 2 * x * P := by positivity
  have hA : |eval NUM x / eval Sh x ^ 2 - (1 / x + 2 * x - 1 / P)| ≤ (η : ℝ) := by
    have heq : eval NUM x * x * P - eval Sh x ^ 2 * (P + 2 * x ^ 2 * P - x) =
        (eval Sh x ^ 2 * x * P) * (eval NUM x / eval Sh x ^ 2 - (1 / x + 2 * x - 1 / P)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hW, mul_comm (η : ℝ)] at hw
    exact le_of_mul_le_mul_left hw hW
  have hF := erfcxN_pos x
  have hFlo : (pmin : ℝ) - σ ≤ erfcxN x := by
    have := (abs_le.mp hσx).1
    linarith
  have hdiff : |1 / erfcxN x - 1 / P| ≤ (σ : ℝ) / (pmin * (pmin - σ)) := by
    rw [div_sub_div _ _ hF.ne' hP.ne', abs_div, abs_of_pos (mul_pos hF hP),
      div_le_div_iff₀ (mul_pos hF hP) (mul_pos hpmin (by linarith))]
    have h1 : |1 * P - erfcxN x * 1| ≤ σ := by
      rw [one_mul, mul_one, abs_sub_comm]
      exact hσx
    have h2 : (pmin : ℝ) * (pmin - σ) ≤ erfcxN x * P := by
      rw [mul_comm (erfcxN x)]
      exact mul_le_mul hpx hFlo (by linarith) hP.le
    calc |1 * P - erfcxN x * 1| * (pmin * (pmin - σ)) ≤ σ * (pmin * (pmin - σ)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hpmin.le (by linarith))
      _ ≤ σ * (erfcxN x * P) := mul_le_mul_of_nonneg_left h2 hσ0
  have hsplit : eval NUM x / eval Sh x ^ 2 - (1 / x + 2 * x - 1 / erfcxN x) =
      (eval NUM x / eval Sh x ^ 2 - (1 / x + 2 * x - 1 / P)) + (1 / erfcxN x - 1 / P) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hA hdiff)

/-- A function on `[a, b]` with derivative at most `M` in magnitude and value at most `α` in
magnitude at `b` stays within `α + M (b - x)`. -/
theorem combine (f f' : ℝ → ℝ) {a b M α : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hM : ∀ x ∈ Icc a b, |f' x| ≤ M) (hb : |f b| ≤ α) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x| ≤ α + M * (b - x) := by
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := f) (a := x) (b := b) (C := M)
    (fun u hu => (hd u ⟨hx.1.trans hu.1, hu.2⟩).hasDerivWithinAt)
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hM u ⟨hx.1.trans hu.1, hu.2.le⟩) b ⟨hx.2, le_rfl⟩
  rw [Real.norm_eq_abs] at hmv
  have h := abs_sub_abs_le_abs_sub (f x) (f b)
  rw [abs_sub_comm] at hmv
  linarith

/-! ### Anchors -/

/-- The model at a rational point, over `ℚ`. -/
def wQ (R S : List ℚ) (x : ℚ) : ℚ := evalQ R (x ^ 2)⁻¹ / evalQ S (x ^ 2)⁻¹ - 9 / 16

theorem tailW_cast (R S : List ℚ) (x : ℚ) : tailW R S x = wQ R S x := by
  rw [tailW, wQ]
  have h : ((x : ℝ) ^ 2)⁻¹ = (((x ^ 2)⁻¹ : ℚ) : ℝ) := by push_cast; rfl
  rw [h, eval_cast, eval_cast]
  push_cast
  rfl

/-- The upper end of the enclosure of `2/√π`. -/
def kappaHi : ℚ := 333038747416263463344 / 2 ^ 68

/-- The rational conditions of an anchor at `x0`: with `E` the exponential's Taylor polynomial of
degree `n - 1` at the model's value `w0` and `e` its remainder bound, the enclosure of
`x0 erfcx x0` from `pv ± σ` lies within a factor `1 + α` of the enclosure of `exp w0`. -/
def anchorOK (R S : List ℚ) (x0 pv σ α : ℚ) (n : ℕ) : Bool :=
  let w0 := wQ R S x0
  let E := evalQ (TaylorRemainder.expCoeffs n) w0
  let e := |w0| ^ n * ((n + 1) / (n.factorial * n))
  let ylo := x0 * kappaLo * (pv - σ)
  let yhi := x0 * kappaHi * (pv + σ)
  decide (0 < x0 ∧ 0 < pv - σ ∧ |w0| ≤ 1 ∧ 0 < E - e ∧ E + e ≤ (1 + α) * ylo ∧
    yhi ≤ (1 + α) * (E - e))

theorem anchor_bound (R S : List ℚ) (x0 pv σ α : ℚ) (n : ℕ) (hn : 0 < n)
    (hok : anchorOK R S x0 pv σ α n = true)
    (hF : |erfcxN x0 - pv| ≤ σ) : |tailF R S x0| ≤ α := by
  simp only [anchorOK, decide_eq_true_eq] at hok
  obtain ⟨hx0, hpv, hw1, hEpos, hup, hdown⟩ := hok
  set w0 := wQ R S x0 with hw0
  set Eq := evalQ (TaylorRemainder.expCoeffs n) w0 with hEq
  set e : ℚ := |w0| ^ n * ((n + 1) / (n.factorial * n)) with he_def
  have hex := TaylorRemainder.exp_remainder (w0 : ℝ) (by exact_mod_cast hw1) n hn
  rw [eval_cast] at hex
  have hcast : ((e : ℚ) : ℝ) = |(w0 : ℝ)| ^ n * ((n + 1 : ℝ) / (n.factorial * n)) := by
    rw [he_def]
    push_cast
    ring
  have he : |exp (w0 : ℝ) - (Eq : ℝ)| ≤ (e : ℝ) := by
    rw [hcast]
    exact hex
  have hup' : (Eq : ℝ) + e ≤ (1 + α) * (x0 * kappaLo * (pv - σ)) := by exact_mod_cast hup
  have hdown' : (x0 : ℝ) * kappaHi * (pv + σ) ≤ (1 + α) * (Eq - e) := by exact_mod_cast hdown
  have hEpos' : (0 : ℝ) < Eq - e := by exact_mod_cast hEpos
  have hpv' : (0 : ℝ) < pv - σ := by exact_mod_cast hpv
  have hx0' : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hσ0 : (0 : ℝ) ≤ σ := (abs_nonneg _).trans hF
  have hk := scale_bounds
  have hkLo : (kappaLo : ℝ) ≤ scale := by rw [kappaLo_cast]; exact hk.1
  have hkHi : scale ≤ (kappaHi : ℝ) := by
    have h : ((kappaHi : ℚ) : ℝ) = 333038747416263463344 / 2 ^ 68 := by simp [kappaHi]
    rw [h]; exact hk.2
  have hs0 := scale_pos
  have hFb := abs_le.mp hF
  have hF0 : 0 < erfcxN (x0 : ℝ) := erfcxN_pos _
  have hy : (x0 : ℝ) * erfcx x0 = x0 * scale * erfcxN x0 := by rw [erfcx_eq]; ring
  have hylo : (x0 : ℝ) * kappaLo * (pv - σ) ≤ x0 * scale * erfcxN x0 := by
    have h1 : (kappaLo : ℝ) * (pv - σ) ≤ scale * erfcxN x0 :=
      mul_le_mul hkLo (by linarith [hFb.1]) hpv'.le hs0.le
    have := mul_le_mul_of_nonneg_left h1 hx0'.le
    linarith
  have hyhi : (x0 : ℝ) * scale * erfcxN x0 ≤ x0 * kappaHi * (pv + σ) := by
    have h1 : scale * erfcxN x0 ≤ (kappaHi : ℝ) * (pv + σ) :=
      mul_le_mul hkHi (by linarith [hFb.2]) hF0.le (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hx0'.le
    linarith
  have hypos : (0 : ℝ) < x0 * scale * erfcxN x0 := by positivity
  have hEb := abs_le.mp he
  have hyhipos : (0 : ℝ) < x0 * kappaHi * (pv + σ) := lt_of_lt_of_le hypos hyhi
  have h1α : (0 : ℝ) < 1 + α := by
    by_contra hneg
    have hneg' : 1 + (α : ℝ) ≤ 0 := not_lt.mp hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg' hEpos'.le
    linarith
  have hexp0 : 0 < exp (w0 : ℝ) := exp_pos _
  have hEy : exp (w0 : ℝ) ≤ (1 + α) * (x0 * scale * erfcxN x0) := by
    have := mul_le_mul_of_nonneg_left hylo h1α.le
    linarith [hEb.2]
  have hyE : (x0 : ℝ) * scale * erfcxN x0 ≤ (1 + α) * exp (w0 : ℝ) := by
    have := mul_le_mul_of_nonneg_left (show (Eq : ℝ) - e ≤ exp (w0 : ℝ) by linarith [hEb.1])
      h1α.le
    linarith
  have hlog : tailF R S x0 = Real.log (exp (w0 : ℝ) / (x0 * scale * erfcxN x0)) := by
    rw [tailF, tailW_cast, hy, Real.log_div hexp0.ne' hypos.ne', Real.log_exp]
  rw [hlog, abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hexp0 hypos)
    rw [inv_div] at h1
    have h2 : (x0 : ℝ) * scale * erfcxN x0 / exp (w0 : ℝ) ≤ 1 + α := by
      rw [div_le_iff₀ hexp0]
      exact hyE
    linarith
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hexp0 hypos)
    have h2 : exp (w0 : ℝ) / (x0 * scale * erfcxN x0) ≤ 1 + α := by
      rw [div_le_iff₀ hypos]
      exact hEy
    linarith

/-! ### Assembly lemmas -/

/-- `asymSum N x` over `ℚ`. -/
def asymQ (N : ℕ) (x : ℚ) : ℚ := x⁻¹ * evalQ ((List.range N).map asymCoeff) (x⁻¹ ^ 2)

theorem asymSum_cast (N : ℕ) (x : ℚ) : asymSum N x = asymQ N x := by
  rw [asymSum_eq, asymQ]
  have h : ((x : ℝ)⁻¹) ^ 2 = ((x⁻¹ ^ 2 : ℚ) : ℝ) := by push_cast; rfl
  rw [h, eval_cast]
  push_cast
  rfl

theorem eval_sub_cast (p : List ℚ) (x c : ℚ) : eval p ((x : ℝ) - c) = ((evalQ p (x - c) : ℚ) : ℝ) := by
  rw [← eval_cast]
  push_cast
  rfl

/-- The start of the chain at `x0`, from the asymptotic bounds with `N` and `N + 1` terms. -/
theorem start_bound (p : List ℚ) (x0 c σ : ℚ) (N : ℕ) (hN : Even N)
    (hok : decide (0 < x0 ∧ evalQ p (x0 - c) - σ ≤ asymQ N x0 / 2 ∧
      asymQ (N + 1) x0 / 2 ≤ evalQ p (x0 - c) + σ) = true) :
    |erfcxN x0 - eval p ((x0 : ℝ) - c)| ≤ σ := by
  simp only [decide_eq_true_eq] at hok
  obtain ⟨hx0, hlo, hhi⟩ := hok
  have hx : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have h1 := erfcxN_asym N hx
  have h2 := erfcxN_asym (N + 1) hx
  rw [hN.neg_one_pow, one_mul, asymSum_cast] at h1
  rw [(hN.add_one).neg_one_pow, asymSum_cast] at h2
  rw [eval_sub_cast, abs_le]
  have hlo' : ((evalQ p (x0 - c) : ℚ) : ℝ) - σ ≤ ((asymQ N x0 : ℚ) : ℝ) / 2 := by exact_mod_cast hlo
  have hhi' : ((asymQ (N + 1) x0 : ℚ) : ℝ) / 2 ≤ ((evalQ p (x0 - c) : ℚ) : ℝ) + σ := by
    exact_mod_cast hhi
  constructor <;> linarith

/-- The chain from one piece to the next at their common end `x`. -/
theorem junction (p q : List ℚ) (cp cq x σp ηp bp σq : ℚ)
    (hmodel : |erfcxN x - eval p ((x : ℝ) - cp)| ≤ (σp : ℝ) + ηp * ((bp : ℝ) - x))
    (hJ : decide (|evalQ p (x - cp) - evalQ q (x - cq)| + (σp + ηp * (bp - x)) ≤ σq) = true) :
    |erfcxN x - eval q ((x : ℝ) - cq)| ≤ σq := by
  simp only [decide_eq_true_eq] at hJ
  have hJ' : |((evalQ p (x - cp) : ℚ) : ℝ) - ((evalQ q (x - cq) : ℚ) : ℝ)| +
      ((σp : ℝ) + ηp * ((bp : ℝ) - x)) ≤ σq := by exact_mod_cast hJ
  rw [eval_sub_cast] at hmodel ⊢
  calc |erfcxN x - ((evalQ q (x - cq) : ℚ) : ℝ)|
      ≤ |erfcxN x - ((evalQ p (x - cp) : ℚ) : ℝ)| +
          |((evalQ p (x - cp) : ℚ) : ℝ) - ((evalQ q (x - cq) : ℚ) : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- A lower bound on a polynomial from a check against a constant. -/
theorem lower_of_check (p : List ℚ) (lo hi m r : ℚ) (d : ℕ)
    (hc : check (subP p [m]) lo hi r d = true) {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    ((m - r : ℚ) : ℝ) ≤ eval p t := by
  have h := check_sound _ _ _ _ _ hc t h1 h2
  rw [eval_subP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have := (abs_le.mp h).1
  push_cast
  linarith

/-- `x ^ (2 n) S (1/x²)` is positive when `S - lo` is checked nonnegative on `[0, smax]`, `lo > 0`, and
`1/x² ≤ smax`. -/
theorem hatP_pos (S : List ℚ) (n : ℕ) (hS : S.length ≤ n + 1) (smax lo M : ℚ) (d : ℕ)
    (hc : check (subP (subP S [lo]) [M]) 0 smax M d = true) (hlo : (0 : ℚ) < lo) {x : ℝ}
    (hx : 0 < x) (hs : (x ^ 2)⁻¹ ≤ smax) : 0 < eval (hatP S n) x := by
  rw [eval_hatP S n hS x hx.ne']
  have h := nonneg_of_bounded _ 0 smax M (bounded_of_check _ _ _ _ _ hc) (x ^ 2)⁻¹
    (by push_cast; positivity) hs
  rw [eval_subP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have hlo' : (0 : ℝ) < lo := by exact_mod_cast hlo
  have : 0 < eval S (x ^ 2)⁻¹ := by linarith
  positivity

/-- The derivative bound of one piece in rational form. -/
theorem piece_deriv (R S : List ℚ) (m n : ℕ) (p : List ℚ) (a b c η M N pm pr σ ηd Md : ℚ)
    (ha : (0 : ℝ) < a)
    (hu : check (addP (subP (checkN (numP (hatP R m) (hatP S n) (2 * (n - m))) (hatP S n) p c)
      (scaleP η (checkW (hatP S n) p c))) [M]) (a - c) (b - c) M 20 = true)
    (hl : check (subP (addP (checkN (numP (hatP R m) (hatP S n) (2 * (n - m))) (hatP S n) p c)
      (scaleP η (checkW (hatP S n) p c))) [N]) (a - c) (b - c) N 20 = true)
    (hSpos : ∀ x ∈ Icc (a : ℝ) b, 0 < eval (hatP S n) x)
    (hpc : check (subP p [pm]) (a - c) (b - c) pr 20 = true)
    (hmodel : ∀ x ∈ Icc (a : ℝ) b, |erfcxN x - eval p (x - c)| ≤ (σ : ℝ) + ηd * ((b : ℝ) - x))
    (hMd : decide (0 ≤ ηd ∧ σ + ηd * (b - a) < pm - pr ∧
      η + (σ + ηd * (b - a)) / ((pm - pr) * ((pm - pr) - (σ + ηd * (b - a)))) ≤ Md) = true) :
    ∀ x ∈ Icc (a : ℝ) b, |eval (numP (hatP R m) (hatP S n) (2 * (n - m))) x /
      eval (hatP S n) x ^ 2 - (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md : ℝ) := by
  simp only [decide_eq_true_eq] at hMd
  obtain ⟨hηd, hσp, hMd⟩ := hMd
  intro x hx
  have hb := deriv_bound R S m n p a b c η M N (pm - pr) (σ + ηd * (b - a)) ha
    (bounded_of_check _ _ _ _ _ hu) (bounded_of_check _ _ _ _ _ hl) hSpos
    (fun y hy => lower_of_check p (a - c) (b - c) pm pr 20 hpc
      (by push_cast; linarith [hy.1]) (by push_cast; linarith [hy.2]))
    (fun y hy => by
      have h := hmodel y hy
      have hηd' : (0 : ℝ) ≤ ηd := by exact_mod_cast hηd
      push_cast
      nlinarith [hy.1])
    (by exact_mod_cast hσp) hx
  have hMd' : (η : ℝ) + ((σ + ηd * (b - a) : ℚ) : ℝ) / (((pm - pr : ℚ) : ℝ) *
      (((pm - pr : ℚ) : ℝ) - ((σ + ηd * (b - a) : ℚ) : ℝ))) ≤ Md := by exact_mod_cast hMd
  linarith

/-- The tail error on a stretch `[a', b']` of a piece, from the anchor at `b'` and the derivative
bound `Md`. -/
theorem sub_bound (R S : List ℚ) (m n : ℕ) (hR : R.length ≤ m + 1) (hS : S.length ≤ n + 1)
    (hmn : m ≤ n) (p : List ℚ) (a b c σ ηd Md : ℚ) (ha : (0 : ℝ) < a)
    (hmodel : ∀ x ∈ Icc (a : ℝ) b, |erfcxN x - eval p (x - c)| ≤ (σ : ℝ) + ηd * ((b : ℝ) - x))
    (hSpos : ∀ x ∈ Icc (a : ℝ) b, 0 < eval (hatP S n) x)
    (hderiv : ∀ x ∈ Icc (a : ℝ) b, |eval (numP (hatP R m) (hatP S n) (2 * (n - m))) x /
      eval (hatP S n) x ^ 2 - (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md : ℝ))
    (a' b' α ε : ℚ)
    (hsub : decide (a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ α + Md * (b' - a') ≤ ε) = true)
    (hok : anchorOK R S b' (evalQ p (b' - c)) (σ + ηd * (b - b')) α 24 = true) :
    ∀ x ∈ Icc (a' : ℝ) b', |tailF R S x| ≤ (ε : ℝ) := by
  simp only [decide_eq_true_eq] at hsub
  obtain ⟨h1, h2, h3, h4⟩ := hsub
  have h1' : (a : ℝ) ≤ a' := by exact_mod_cast h1
  have h3' : (b' : ℝ) ≤ b := by exact_mod_cast h3
  have h2' : (a' : ℝ) ≤ b' := by exact_mod_cast h2
  have hF : |erfcxN b' - ((evalQ p (b' - c) : ℚ) : ℝ)| ≤ ((σ + ηd * (b - b') : ℚ) : ℝ) := by
    have h := hmodel b' ⟨h1'.trans h2', h3'⟩
    rw [eval_sub_cast] at h
    push_cast
    exact h
  have han := anchor_bound R S b' (evalQ p (b' - c)) (σ + ηd * (b - b')) α 24 (by norm_num) hok hF
  intro x hx
  have hxab : ∀ y ∈ Icc (a' : ℝ) b', y ∈ Icc (a : ℝ) b := fun y hy => ⟨h1'.trans hy.1, hy.2.trans h3'⟩
  have hc := combine (tailF R S) (fun y => eval (numP (hatP R m) (hatP S n) (2 * (n - m))) y /
      eval (hatP S n) y ^ 2 - (1 / y + 2 * y - 1 / erfcxN y))
    (fun y hy => hasDerivAt_tailF R S m n hR hS hmn (lt_of_lt_of_le ha (hxab y hy).1)
      (hSpos y (hxab y hy)).ne')
    (fun y hy => hderiv y (hxab y hy)) han hx
  have hMd0 : (0 : ℝ) ≤ Md := (abs_nonneg _).trans (hderiv x (hxab x hx))
  have h4' : (α : ℝ) + Md * (b' - a') ≤ ε := by exact_mod_cast h4
  have : (Md : ℝ) * (b' - x) ≤ Md * (b' - a') := mul_le_mul_of_nonneg_left (by linarith [hx.1]) hMd0
  linarith

#print axioms tailW_eq
#print axioms hasDerivAt_tailF
#print axioms eval_checkN
#print axioms piece_model
#print axioms deriv_bound
#print axioms combine
#print axioms anchor_bound
#print axioms start_bound
#print axioms junction
#print axioms hatP_pos
#print axioms piece_deriv
#print axioms sub_bound

end Library.Numerics.Float64.Erf.ErfTailBase
