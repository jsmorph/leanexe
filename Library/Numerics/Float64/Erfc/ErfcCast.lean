import LeanExe.ProofKit.PolyBound

/-!
`qc h` transfers a rational fact `h` to the reals: an inequality or equality between rationals
becomes the same statement between their casts, with the casts pushed inward on both sides and
`linarith` closing the goal.  It falls back to `exact_mod_cast` for other casts.
-/

macro "qc " h:term : tactic =>
  `(tactic| first
    | (have hq := (Rat.cast_le (K := ℝ)).mpr $h; push_cast at hq ⊢; linarith)
    | (have hq := (Rat.cast_lt (K := ℝ)).mpr $h; push_cast at hq ⊢; linarith)
    | (have hq := congrArg (fun q : ℚ => (q : ℝ)) $h; push_cast at hq ⊢; linarith)
    | exact_mod_cast $h)

theorem qc_example (a b : ℚ) (h : a ≤ b / 2 ^ 53) : (a : ℝ) ≤ b / 2 ^ 53 := by qc h

#print axioms qc_example
