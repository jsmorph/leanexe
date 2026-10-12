import LeanExe.ProofKit.TaylorModel

/-!
A kernel check that an expression stays within `ε` of zero on `[-r, r]`: `exprOk c E ε depth`
computes the Taylor model of `E` and checks its polynomial against `ε` less the model's error with
`PolyBound.check`, and `exprOk_sound` gives `|E.eval t| ≤ ε` for `|t| ≤ r`.  With `E` the
difference of a function and its approximation, this bounds the approximation's error; with
`r = 0`, it encloses a constant such as a table entry.
-/

namespace LeanExe.ProofKit.TaylorCheck

open PolyBound TaylorModel

/-- The kernel check that `|E t| ≤ ε` for `|t| ≤ r`. -/
def exprOk (c : Cfg) (E : Expr) (ε : ℚ) (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) &&
    match tm c E with
    | some T => check T.p (-c.r) c.r (ε - T.e) depth
    | none => false

theorem exprOk_sound (c : Cfg) (E : Expr) (ε : ℚ) (depth : ℕ)
    (hpi : (c.piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ c.piHi) (h : exprOk c E ε depth = true) {t : ℝ}
    (ht : |t| ≤ c.r) : |E.eval t| ≤ ε := by
  simp only [exprOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hr, hm⟩ := h
  cases hT : tm c E with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    have htr := abs_le.mp ht
    have hc := check_sound _ _ _ _ _ hm t (by push_cast; linarith) (by linarith)
    have h2 := tm_sound c hr hpi E hT t ht
    push_cast at hc
    calc |E.eval t| = |(E.eval t - eval T.p t) + eval T.p t| := by ring_nf
      _ ≤ |E.eval t - eval T.p t| + |eval T.p t| := abs_add_le _ _
      _ ≤ _ := by linarith

#print axioms exprOk_sound

end LeanExe.ProofKit.TaylorCheck
