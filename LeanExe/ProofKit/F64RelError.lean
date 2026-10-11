import LeanExe.ProofKit.F64Approx

/-!
Relative error tracking for positive values over wide ranges.  `RApprox w v ρ` states that `w` is
finite and within `ρ v` of the positive real `v`.  Each operation lemma follows from the absolute
lemma of `F64Approx` with magnitude bounds proportional to `v`: a rounding adds `2 ^ -53` of the
bound, and a product or quotient adds an underflow term `η` with `2 ^ -1075 ≤ η` times the value.
-/

namespace LeanExe.ProofKit.F64RelError
open CodeLib.IEEE64 F64Approx

def RApprox (w : UInt64) (v ρ : ℝ) : Prop := 0 < v ∧ Approx w v (ρ * v)

theorem RApprox.rho_nonneg {w : UInt64} {v ρ : ℝ} (h : RApprox w v ρ) : 0 ≤ ρ := by
  have h0 := (abs_nonneg _).trans h.2.2
  exact nonneg_of_mul_nonneg_left h0 h.1

theorem RApprox.mono {w : UInt64} {v ρ ρ' : ℝ} (h : RApprox w v ρ) (hρ : ρ ≤ ρ') :
    RApprox w v ρ' :=
  ⟨h.1, h.2.mono (mul_le_mul_of_nonneg_right hρ h.1.le)⟩

theorem rapprox_self (w : UInt64) (hw : Finite w) (hv : 0 < value w) : RApprox w (value w) 0 :=
  ⟨hv, by rw [zero_mul]; exact approx_self w hw⟩

theorem RApprox.bounds {w : UInt64} {v ρ : ℝ} (h : RApprox w v ρ) :
    (1 - ρ) * v ≤ value w ∧ value w ≤ (1 + ρ) * v := by
  have h1 := abs_le.mp h.2.2
  constructor <;> nlinarith [h1.1, h1.2]

theorem rapprox_mul {a b : UInt64} {va vb ρa ρb : ℝ} (ha : RApprox a va ρa)
    (hb : RApprox b vb ρb) (η : ℝ) (hη : 1 / 2 ^ 1075 ≤ η * (va * vb))
    (hov : (1 + ρa) * (1 + ρb) * (va * vb) < 2 ^ 1022) :
    RApprox (Wasm.IEEE64.mul a b) (va * vb)
      (ρa + ρb + ρa * ρb + (1 + ρa) * (1 + ρb) / 2 ^ 53 + η) := by
  have hρa := ha.rho_nonneg
  have hρb := hb.rho_nonneg
  have h := approx_mul ha.2 hb.2 va vb (abs_of_pos ha.1).le (abs_of_pos hb.1).le
    ((1 + ρa) * (1 + ρb) * (va * vb)) (le_of_eq (by ring)) hov
  refine ⟨mul_pos ha.1 hb.1, h.mono ?_⟩
  calc _ = (ρa + ρb + ρa * ρb + (1 + ρa) * (1 + ρb) / 2 ^ 53) * (va * vb) + 1 / 2 ^ 1075 := by
        ring
    _ ≤ _ := by linarith

/-- A sum of positive values, with a bound `θ` on the weighted relative errors. -/
theorem rapprox_add {a b : UInt64} {va vb ρa ρb : ℝ} (ha : RApprox a va ρa)
    (hb : RApprox b vb ρb) (θ : ℝ) (hθ : ρa * va + ρb * vb ≤ θ * (va + vb))
    (hov : (1 + θ) * (va + vb) < 2 ^ 1023) :
    RApprox (Wasm.IEEE64.add a b) (va + vb) (θ + (1 + θ) / 2 ^ 53) := by
  have hρa := ha.rho_nonneg
  have hρb := hb.rho_nonneg
  have hs : 0 < va + vb := add_pos ha.1 hb.1
  have hθ0 : 0 ≤ θ := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hρa ha.1.le, mul_nonneg hρb hb.1.le]
  have h := approx_add ha.2 hb.2 ((1 + θ) * (va + vb)) (by rw [abs_of_pos hs]; linarith) hov
  refine ⟨hs, h.mono ?_⟩
  calc _ ≤ θ * (va + vb) + (1 + θ) * (va + vb) / 2 ^ 53 := by linarith
    _ = _ := by ring

/-- A difference of positive values `va > vb`, with a bound `θ` on the weighted errors. -/
theorem rapprox_sub {a b : UInt64} {va vb ρa ρb : ℝ} (ha : RApprox a va ρa)
    (hb : RApprox b vb ρb) (hab : vb < va) (θ : ℝ) (hθ : ρa * va + ρb * vb ≤ θ * (va - vb))
    (hov : (1 + θ) * (va - vb) < 2 ^ 1023) :
    RApprox (Wasm.IEEE64.sub a b) (va - vb) (θ + (1 + θ) / 2 ^ 53) := by
  have hρa := ha.rho_nonneg
  have hρb := hb.rho_nonneg
  have hs : 0 < va - vb := by linarith
  have h := approx_sub ha.2 hb.2 ((1 + θ) * (va - vb)) (by
    rw [abs_of_pos hs]
    nlinarith [mul_nonneg hρa ha.1.le, mul_nonneg hρb hb.1.le]) hov
  refine ⟨hs, h.mono ?_⟩
  calc _ ≤ θ * (va - vb) + (1 + θ) * (va - vb) / 2 ^ 53 := by linarith
    _ = _ := by ring

theorem rapprox_div {a b : UInt64} {va vb ρa ρb : ℝ} (ha : RApprox a va ρa)
    (hb : RApprox b vb ρb) (hρb1 : ρb < 1) (η : ℝ) (hη : 1 / 2 ^ 1075 ≤ η * (va / vb))
    (hov : (1 + ρa) / (1 - ρb) * (va / vb) < 2 ^ 1022) :
    RApprox (Wasm.IEEE64.div a b) (va / vb)
      ((ρa + ρb) / (1 - ρb) + (1 + ρa) / (1 - ρb) / 2 ^ 53 + η) := by
  have hρa := ha.rho_nonneg
  have hρb := hb.rho_nonneg
  have hq : 0 < va / vb := div_pos ha.1 hb.1
  have hd : 0 < 1 - ρb := by linarith
  have hvb : vb ≠ 0 := hb.1.ne'
  have hd' : 1 - ρb ≠ 0 := hd.ne'
  have hvd : vb - ρb * vb ≠ 0 := by
    have : 0 < vb - ρb * vb := by nlinarith [hb.1]
    exact this.ne'
  have h := approx_div ha.2 hb.2 va vb (abs_of_pos ha.1).le (abs_of_pos hb.1).ge
    (by nlinarith [hb.1]) ((1 + ρa) / (1 - ρb) * (va / vb))
    (le_of_eq (by field_simp)) hov
  refine ⟨hq, h.mono ?_⟩
  have h3 : (ρa * va + va * (ρb * vb) / vb) / (vb - ρb * vb) =
      (ρa + ρb) / (1 - ρb) * (va / vb) := by
    field_simp
  calc _ = (ρa + ρb) / (1 - ρb) * (va / vb) +
        (1 + ρa) / (1 - ρb) / 2 ^ 53 * (va / vb) + 1 / 2 ^ 1075 := by rw [h3]; ring
    _ ≤ _ := by linarith

theorem rapprox_sqrt {a : UInt64} {va ρa : ℝ} (ha : RApprox a va ρa) (hρa1 : ρa < 1) :
    RApprox (Wasm.IEEE64.sqrt a) (Real.sqrt va) (ρa + (1 + ρa) / 2 ^ 53) := by
  have hρa := ha.rho_nonneg
  have hs : 0 < Real.sqrt va := Real.sqrt_pos.mpr ha.1
  have hsq : Real.sqrt va * Real.sqrt va = va := Real.mul_self_sqrt ha.1.le
  have hS : Real.sqrt (va + ρa * va) ≤ (1 + ρa) * Real.sqrt va := by
    rw [Real.sqrt_le_left (mul_nonneg (by linarith) (Real.sqrt_nonneg _)), mul_pow,
      Real.sq_sqrt ha.1.le]
    nlinarith [mul_nonneg (mul_nonneg hρa hρa) ha.1.le]
  have h := approx_sqrt ha.2 va va ha.1 le_rfl (by nlinarith [ha.1]) le_rfl _ hS
  refine ⟨hs, h.mono ?_⟩
  have h3 : ρa * va / Real.sqrt va = ρa * Real.sqrt va := by
    rw [div_eq_iff hs.ne', mul_assoc, hsq]
  calc _ = (ρa + (1 + ρa) / 2 ^ 53) * Real.sqrt va := by rw [h3]; ring
    _ ≤ _ := le_rfl

#print axioms rapprox_mul
#print axioms rapprox_add
#print axioms rapprox_sub
#print axioms rapprox_div
#print axioms rapprox_sqrt

end LeanExe.ProofKit.F64RelError
