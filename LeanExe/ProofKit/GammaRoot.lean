import LeanExe.ProofKit.GammaReflect
import LeanExe.ProofKit.GammaConvex
import LeanExe.ProofKit.PolyChecks

/-!
Taylor models of `lgamma` on intervals of negative numbers, and the kernel check of CORE-MATH's
polynomials about the negative zeros of `lgamma` against them.  For `x = -n - (δ + t)` with
`0 < δ + t < 1`, `lgamma x = log π - log (sin (π (δ + t))) - lgamma (n + 1 + δ + t)`, and `negVar`
models it in `t`, with the sine's argument reduced as in `GammaReflect.sinPiExpr` (`sinPiVar`).
`rootOk` computes the Taylor models `T` of `negVar` and `U` of an expression `Q` and checks, with a
sign `σ`, a floor `m0`, and a slack `s0`, that `|T - U| ≤ s0 + ε σ T` and `σ T ≥ m0`;
`rootOk_sound` gives `|lgamma x - Q| ≤ ε' |lgamma x| + S`.  The slack lets the check cover the
zero of `lgamma`, where no relative bound holds, and `m0` the pieces away from it.  `root_piece`
states the bound in `x` for CORE-MATH's form `(x + x0) R (2 ^ e (x + x0))`, and `root_domain_dec`
and `root_domain_inc` confine the points where `|lgamma x| ≤ c` to an interval `[A, B]` around the
zero, from the convexity of `lgamma` between two poles and its values at `A`, `B`, and one end.
-/

namespace LeanExe.ProofKit.GammaRoot

open Real Set PolyBound PolyChecks TaylorModel TaylorCheck GammaBasic GammaModels GammaReflect
  GammaConvex

/-- The kernel check that `p ≤ s` on `[-r, r]`. -/
def upperOk (p : List ℚ) (r s : ℚ) (depth : ℕ) : Bool :=
  check (addP (addP p [-s]) [absSum r (addP p [-s])]) (-r) r (absSum r (addP p [-s])) depth

theorem upperOk_sound (p : List ℚ) (r s : ℚ) (depth : ℕ) (h : upperOk p r s depth = true)
    {t : ℝ} (ht : |t| ≤ r) : eval p t ≤ s := by
  have htr := abs_le.mp ht
  have hb := nonpos_of_bounded (addP p [-s]) (-r) r _ (bounded_of_check _ _ _ _ _ h) t
    (by push_cast; linarith) htr.2
  rw [eval_addP] at hb
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hb
  push_cast at hb
  linarith

/-- `sin (π (δ + t))` with an argument of at most `0.3 π` for the sine and `0.2 π` for the cosine
at `t = 0`. -/
def sinPiVar (δ : ℚ) : Expr :=
  if δ ≤ 1 / 2 then
    if δ ≤ 3 / 10 then .sin (.mul .pi (.poly [δ, 1]))
    else .cos (.mul .pi (.poly [1 / 2 - δ, -1]))
  else
    if 1 - δ ≤ 3 / 10 then .sin (.mul .pi (.poly [1 - δ, -1]))
    else .cos (.mul .pi (.poly [δ - 1 / 2, 1]))

theorem sinPiVar_eval (δ : ℚ) (t : ℝ) : (sinPiVar δ).eval t = Real.sin (π * (δ + t)) := by
  unfold sinPiVar
  split_ifs <;> simp only [Expr.eval, eval_cons, eval_nil] <;> try push_cast
  · congr 1
    ring
  · conv_rhs => rw [← Real.cos_pi_div_two_sub]
    congr 1
    ring
  · conv_rhs => rw [← Real.sin_pi_sub]
    congr 1
    ring
  · conv_rhs => rw [← Real.cos_sub_pi_div_two]
    congr 1
    ring

/-- `log (sin (π (δ + t)))` as `log q + log (1 + (sin (π (δ + t))/q - 1))`. -/
def logSinVar (δ q : ℚ) (d : LogData) (l2lo l2hi : ℚ) : Expr :=
  .add (logQExpr q d l2lo l2hi) (.log1p (.add (.mul (.const (1 / q)) (sinPiVar δ)) (.const (-1))))

theorem logSinVar_eval (δ q : ℚ) (hq : 0 < q) (d : LogData) (l2lo l2hi : ℚ) (t : ℝ)
    (hs : 0 < Real.sin (π * (δ + t))) :
    (logSinVar δ q d l2lo l2hi).eval t = Real.log (Real.sin (π * (δ + t))) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [logSinVar, Expr.eval]
  rw [logQExpr_eval q hq, sinPiVar_eval]
  push_cast
  rw [show (1 : ℝ) + (1 / q * Real.sin (π * (δ + t)) + -1) = Real.sin (π * (δ + t)) / q by ring,
    Real.log_div hs.ne' hq'.ne']
  ring

/-- The model of `lgamma (-n - (δ + t))` with `d` a model of `lgamma` at `n + 1 + δ`. -/
def negVar (δ q : ℚ) (ds : LogData) (d : LgData) : Expr :=
  Expr.sub (Expr.sub (logPiExpr d.l2lo d.l2hi) (logSinVar δ q ds d.l2lo d.l2hi)) (lgammaExpr d)

/-- `(c - t) R (2 ^ e (c - t))`: a polynomial about a zero in `x + x0 = c - t`. -/
def rootQ (c : ℚ) (e : ℕ) (R : List ℚ) : Expr :=
  .mul (.poly [c, -1]) (.polyOf R (.poly [2 ^ e * c, -2 ^ e]))

theorem rootQ_eval (c : ℚ) (e : ℕ) (R : List ℚ) (t : ℝ) :
    (rootQ c e R).eval t = (c - t) * eval R (2 ^ e * (c - t)) := by
  simp only [rootQ, Expr.eval, eval_cons, eval_nil]
  push_cast
  congr 1
  · ring
  · congr 1
    ring

/-- The kernel check of `Q` against `lgamma (-n - (δ + t))` for `|t| ≤ r`. -/
def rootOk (c : Cfg) (n : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (Q : Expr)
    (σ ε ε' m0 s0 S : ℚ) (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (c.r < δ) && decide (δ + c.r < 1) && decide (0 < q) &&
    decide (d.a = n + 1 + δ) && decide (16 + c.r ≤ d.a + d.n) && decide (σ = 1 ∨ σ = -1) &&
    decide (0 ≤ ε) && decide (ε ≤ ε') &&
    match tm c (negVar δ q ds d), tm c Q with
    | some T, some U =>
      upperOk (subP (subP T.p U.p) (scaleP ε (scaleP σ T.p))) c.r s0 depth &&
        upperOk (subP (scaleP (-1) (subP T.p U.p)) (scaleP ε (scaleP σ T.p))) c.r s0 depth &&
        upperOk (subP [m0] (scaleP σ T.p)) c.r 0 depth &&
        decide (s0 + (1 + ε) * (T.e + stirRemQ d c.r) + U.e ≤
          (ε' - ε) * max 0 (m0 - (T.e + stirRemQ d c.r)) + S)
    | _, _ => false

theorem rootOk_sound (c : Cfg) (n : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (Q : Expr)
    (σ ε ε' m0 s0 S : ℚ) (depth : ℕ) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi)
    (h : rootOk c n δ q ds d Q σ ε ε' m0 s0 S depth = true) {t : ℝ} (ht : |t| ≤ c.r) :
    |lgamma (-n - (δ + t)) - Q.eval t| ≤ ε' * |lgamma (-n - (δ + t))| + S := by
  simp only [rootOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hrδ⟩, hδr⟩, hq⟩, hda⟩, hY⟩, hσ⟩, hε⟩, hεε⟩, hm⟩ := h
  have htr := abs_le.mp ht
  have hrδ' : (c.r : ℝ) < δ := by exact_mod_cast hrδ
  have hδr' : (δ : ℝ) + c.r < 1 := by exact_mod_cast hδr
  have h0 : 0 < (δ : ℝ) + t := by linarith
  have h1 : (δ : ℝ) + t < 1 := by linarith
  have hspos : 0 < Real.sin (π * (δ + t)) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])
  have hra : c.r < d.a := by
    rw [hda]
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs := lgamma_sub_expr_le d hr hra hY ht
  rw [stirRem_eq] at hs
  have hda' : ((d.a : ℚ) : ℝ) + t = n + 1 + (δ + t) := by
    rw [hda]
    push_cast
    ring
  rw [hda'] at hs
  have hneg : (negVar δ q ds d).eval t =
      Real.log π - Real.log (Real.sin (π * (δ + t))) - (lgammaExpr d).eval t := by
    simp only [negVar, Expr.sub, Expr.eval]
    rw [logPiExpr_eval, logSinVar_eval δ q hq ds d.l2lo d.l2hi t hspos]
    ring
  cases hT : tm c (negVar δ q ds d) with
  | none => simp [hT] at hm
  | some T =>
    cases hU : tm c Q with
    | none => simp [hT, hU] at hm
    | some U =>
      simp only [hT, hU, Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hfin⟩ := hm
      have hTa := tm_sound c hr hpi _ hT t ht
      have hUa := tm_sound c hr hpi _ hU t ht
      rw [hneg] at hTa
      have u1 := upperOk_sound _ _ _ _ hc1 ht
      have u2 := upperOk_sound _ _ _ _ hc2 ht
      have u3 := upperOk_sound _ _ _ _ hc3 ht
      simp only [eval_subP, eval_scaleP, eval_cons, eval_nil, mul_zero, add_zero] at u1 u2 u3
      push_cast at u1 u2 u3
      have tri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
      set f := lgamma (-n - (δ + t)) with hfdef
      set p := eval T.p t
      set P := eval U.p t
      set e1 : ℚ := T.e + stirRemQ d c.r with he1
      have hfp : |f - p| ≤ e1 := by
        have e : f - p = ((Real.log π - Real.log (Real.sin (π * (δ + t))) -
            (lgammaExpr d).eval t) - p) - (lgamma (n + 1 + (δ + t)) - (lgammaExpr d).eval t) := by
          rw [hfdef, lgamma_neg_point n h0 h1]
          ring
        rw [e, he1]
        push_cast
        exact (tri _ _).trans (add_le_add hTa hs)
      have hσ' : (σ : ℝ) = 1 ∨ (σ : ℝ) = -1 := by
        rcases hσ with h | h
        · left
          rw [h]
          norm_num
        · right
          rw [h]
          norm_num
      have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
      have hεε' : (0 : ℝ) ≤ ε' - ε := by
        have : (ε : ℝ) ≤ ε' := by exact_mod_cast hεε
        linarith
      have hfinr : (s0 : ℝ) + (1 + ε) * e1 + U.e ≤ (ε' - ε) * max 0 ((m0 : ℝ) - e1) + S := by
        exact_mod_cast hfin
      have hpf : |p| ≤ |f| + e1 := by
        have h1 := abs_sub_abs_le_abs_sub p f
        rw [abs_sub_comm] at h1
        linarith
      have hσp : (σ : ℝ) * p ≤ |f| + e1 := by
        rcases hσ' with h | h <;> rw [h]
        · linarith [le_abs_self p]
        · linarith [neg_abs_le p]
      have hσf : (σ : ℝ) * p - e1 ≤ |f| := by
        have hb := abs_le.mp hfp
        rcases hσ' with h | h <;> rw [h]
        · linarith [le_abs_self f, hb.1]
        · linarith [neg_abs_le f, hb.2]
      have hmax : max 0 ((m0 : ℝ) - e1) ≤ |f| := max_le (abs_nonneg f) (by linarith)
      have hA : |p - P| ≤ s0 + ε * (σ * p) := by
        rw [abs_le]
        constructor <;> linarith
      have hgP : |Q.eval t - P| ≤ U.e := hUa
      have k1 := mul_le_mul_of_nonneg_left hσp hεr
      have k2 := mul_le_mul_of_nonneg_left hmax hεε'
      calc |f - Q.eval t| = |(f - p) + (p - P) - (Q.eval t - P)| := by ring_nf
        _ ≤ |(f - p) + (p - P)| + |Q.eval t - P| := tri _ _
        _ ≤ |f - p| + |p - P| + |Q.eval t - P| := by linarith [abs_add_le (f - p) (p - P)]
        _ ≤ ε' * |f| + S := by linarith

theorem root_piece (cf : Cfg) (m : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (x0 : ℚ) (e : ℕ)
    (R : List ℚ) (σ ε ε' m0 s0 S : ℚ) (depth : ℕ) (hpi : (cf.piLo : ℝ) ≤ π ∧ π ≤ cf.piHi)
    (h : rootOk cf m δ q ds d (rootQ (-m - δ + x0) e R) σ ε ε' m0 s0 S depth = true) {x : ℝ}
    (hx : |x - (-m - δ)| ≤ cf.r) :
    |lgamma x - (x + x0) * eval R (2 ^ e * (x + x0))| ≤ ε' * |lgamma x| + S := by
  have hb := rootOk_sound cf m δ q ds d _ σ ε ε' m0 s0 S depth hpi h (t := -m - δ - x)
    (by rw [abs_sub_comm]; exact hx)
  rw [rootQ_eval] at hb
  have e1 : -(m : ℝ) - (δ + (-m - δ - x)) = x := by ring
  have e2 : (((-m - δ + x0 : ℚ)) : ℝ) - (-m - δ - x) = x + x0 := by
    push_cast
    ring
  rw [e1, e2] at hb
  exact hb

/-- Where `lgamma` decreases through its zero between `A` and `B`, and `hi` is a regular point of
the pole interval, `|lgamma x| ≤ c` holds only on `[A, B]`. -/
theorem root_domain_dec (m : ℕ) {lo hi A B c x : ℝ} (hlo : -(m : ℝ) - 1 ≤ lo) (hhi : hi < -m)
    (hA : lo < A) (hAB : A < B) (hB : B < hi) (hc : 0 ≤ c) (fA : c < lgamma A)
    (fB : lgamma B < -c) (fhi : lgamma hi < -c) (hx1 : lo < x) (hx2 : x < hi)
    (hxc : |lgamma x| ≤ c) : A ≤ x ∧ x ≤ B := by
  have hf := convexOn_lgamma_neg m
  have hxs : x ∈ Ioo (-(m : ℝ) - 1) (-m) := ⟨by linarith, by linarith⟩
  have hBs : B ∈ Ioo (-(m : ℝ) - 1) (-m) := ⟨by linarith, by linarith⟩
  have hhis : hi ∈ Ioo (-(m : ℝ) - 1) (-m) := ⟨by linarith, hhi⟩
  have hb := abs_le.mp hxc
  constructor
  · by_contra hn
    have hlt := not_le.mp hn
    have := convex_left hf hxs hBs hlt.le hAB (by linarith) (by linarith)
    linarith
  · by_contra hn
    have hlt := not_le.mp hn
    have := convex_mid hf hBs hhis hlt.le hx2.le
    have : max (lgamma B) (lgamma hi) < -c := max_lt fB fhi
    linarith

/-- The mirror image of `root_domain_dec`: `lgamma` increases through its zero, and `lo` is a
regular point. -/
theorem root_domain_inc (m : ℕ) {lo hi A B c x : ℝ} (hlo : -(m : ℝ) - 1 < lo) (hhi : hi ≤ -m)
    (hA : lo < A) (hAB : A < B) (hB : B < hi) (hc : 0 ≤ c) (fA : lgamma A < -c)
    (fB : c < lgamma B) (flo : lgamma lo < -c) (hx1 : lo < x) (hx2 : x < hi)
    (hxc : |lgamma x| ≤ c) : A ≤ x ∧ x ≤ B := by
  have hf := convexOn_lgamma_neg m
  have hxs : x ∈ Ioo (-(m : ℝ) - 1) (-m) := ⟨by linarith, by linarith⟩
  have hAs : A ∈ Ioo (-(m : ℝ) - 1) (-m) := ⟨by linarith, by linarith⟩
  have hlos : lo ∈ Ioo (-(m : ℝ) - 1) (-m) := ⟨hlo, by linarith⟩
  have hb := abs_le.mp hxc
  constructor
  · by_contra hn
    have hlt := not_le.mp hn
    have := convex_mid hf hlos hAs hx1.le hlt.le
    have : max (lgamma lo) (lgamma A) < -c := max_lt flo fA
    linarith
  · by_contra hn
    have hlt := not_le.mp hn
    have := convex_right hf hxs hAs hlt.le hAB (by linarith) (by linarith)
    linarith

#print axioms upperOk_sound
#print axioms sinPiVar_eval
#print axioms rootQ_eval
#print axioms rootOk_sound
#print axioms root_piece
#print axioms root_domain_dec
#print axioms root_domain_inc

end LeanExe.ProofKit.GammaRoot
