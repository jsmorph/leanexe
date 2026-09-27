import Project.ExpWide.Reduction
import Project.ProofKit.F64Square

namespace Project.ExpWide
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem evaluate_error (x : UInt64) (hf : Finite x)
    (hl : -8 ≤ value x) (hu : value x ≤ 0) :
    Finite (evaluate x) ∧ 1/100000 ≤ value (evaluate x) ∧
    |value (evaluate x) - Real.exp (value x)| ≤ 1/400 := by
  let a := ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000)
  let r := Real.exp (value x/8)
  have h0 := reduced_polynomial x hf hl hu
  have hb : 1/3 ≤ r ∧ r ≤ 1 :=
    ExpSmall.exp_negative_unit_bounds _ (by linarith) (by linarith)
  have hv : 0 ≤ r := (Real.exp_pos _).le
  have ha : 1/4 ≤ value a := by
    have hh := (abs_le.mp h0.2).1
    change -(1/3990:ℝ) ≤ value a-r at hh
    linarith
  have h1 := F64Square.approximation a r (1/3990) (1/4) h0.1 ⟨hv, hb.2⟩
    h0.2 (by norm_num) (by norm_num) ha
  have hl1 : 1/17 ≤ value (Wasm.IEEE64.mul a a) := h1.2.1.trans' (by norm_num [arithmeticEpsilon])
  have he1 : |value (Wasm.IEEE64.mul a a)-r^2| ≤ 1/1900 :=
    h1.2.2.trans (by norm_num [arithmeticEpsilon])
  have hb1 : 0 ≤ r^2 ∧ r^2 ≤ 1 := ⟨sq_nonneg _, by nlinarith⟩
  let b := Wasm.IEEE64.mul a a
  have h2 := F64Square.approximation b (r^2) (1/1900) (1/17) h1.1 hb1
    he1 (by norm_num) (by norm_num) hl1
  have hl2 : 1/300 ≤ value (Wasm.IEEE64.mul b b) := h2.2.1.trans' (by norm_num [arithmeticEpsilon])
  have he2 : |value (Wasm.IEEE64.mul b b)-(r^2)^2| ≤ 1/900 :=
    h2.2.2.trans (by norm_num [arithmeticEpsilon])
  have hb2 : 0 ≤ (r^2)^2 ∧ (r^2)^2 ≤ 1 := ⟨sq_nonneg _, by nlinarith [hb1.2]⟩
  let c := Wasm.IEEE64.mul b b
  have h3 := F64Square.approximation c ((r^2)^2) (1/900) (1/300) h2.1 hb2
    he2 (by norm_num) (by norm_num) hl2
  refine ⟨h3.1, h3.2.1.trans' (by norm_num [arithmeticEpsilon]), ?_⟩
  have hpower : ((r^2)^2)^2 = Real.exp (value x) := by
    dsimp [r]
    simp only [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hpower] at h3
  exact h3.2.2.trans (by norm_num [arithmeticEpsilon])

#print axioms evaluate_error
end Project.ExpWide
