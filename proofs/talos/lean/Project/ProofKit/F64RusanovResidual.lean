import Project.ProofKit.F64RoundingResidual

namespace Project.ProofKit.F64RusanovResidual
open CodeLib.IEEE64
open Project.ProofKit.F64RoundingResidual
noncomputable section

def Certificate (factor alpha fluxL fluxR stateL stateR output : UInt64) : Prop :=
  ∃ sumError meanError jumpError viscosityError halfError subtractionError : ℝ,
    value output = value factor * (value fluxL + value fluxR - value alpha * (value stateR - value stateL)) +
      value factor * sumError + meanError - value factor * value alpha * jumpError -
      value factor * viscosityError - halfError + subtractionError ∧
    |sumError| ≤ radius (Wasm.IEEE64.add fluxL fluxR) ∧
    |meanError| ≤ radius (Wasm.IEEE64.mul factor (Wasm.IEEE64.add fluxL fluxR)) ∧
    |jumpError| ≤ radius (Wasm.IEEE64.sub stateR stateL) ∧
    |viscosityError| ≤ radius (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL)) ∧
    |halfError| ≤ radius (Wasm.IEEE64.mul factor (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL))) ∧
    |subtractionError| ≤ radius output

theorem rounded_component (factor alpha fluxL fluxR stateL stateR : UInt64)
    (hf : CodeLib.IEEE64.Finite factor) (ha : CodeLib.IEEE64.Finite alpha)
    (hfl : CodeLib.IEEE64.Finite fluxL) (hfr : CodeLib.IEEE64.Finite fluxR)
    (hsl : CodeLib.IEEE64.Finite stateL) (hsr : CodeLib.IEEE64.Finite stateR)
    (hsum : CodeLib.IEEE64.Finite (Wasm.IEEE64.add fluxL fluxR))
    (hmean : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul factor (Wasm.IEEE64.add fluxL fluxR)))
    (hjump : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub stateR stateL))
    (hvisc : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL)))
    (hhalf : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul factor (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL))))
    (hresult : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub
      (Wasm.IEEE64.mul factor (Wasm.IEEE64.add fluxL fluxR))
      (Wasm.IEEE64.mul factor (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL))))) :
    Certificate factor alpha fluxL fluxR stateL stateR (Wasm.IEEE64.sub
      (Wasm.IEEE64.mul factor (Wasm.IEEE64.add fluxL fluxR))
      (Wasm.IEEE64.mul factor (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL)))) := by
  let sum := Wasm.IEEE64.add fluxL fluxR
  let mean := Wasm.IEEE64.mul factor sum
  let jump := Wasm.IEEE64.sub stateR stateL
  let viscosity := Wasm.IEEE64.mul alpha jump
  let half := Wasm.IEEE64.mul factor viscosity
  let output := Wasm.IEEE64.sub mean half
  refine ⟨value sum - (value fluxL + value fluxR),
    value mean - value factor * value sum,
    value jump - (value stateR - value stateL),
    value viscosity - value alpha * value jump,
    value half - value factor * value viscosity,
    value output - (value mean - value half),
    by ring, add_error _ _ hfl hfr hsum, mul_error _ _ hf hsum hmean,
    sub_error _ _ hsr hsl hjump, mul_error _ _ ha hjump hvisc,
    mul_error _ _ hf hvisc hhalf, sub_error _ _ hmean hhalf hresult⟩

def residual (factor alpha fluxL fluxR stateL stateR output : UInt64) : ℝ :=
  value output - value factor *
    (value fluxL + value fluxR - value alpha * (value stateR - value stateL))

def errorBound (factor alpha fluxL fluxR stateL stateR output : UInt64) : ℝ :=
  value factor * radius (Wasm.IEEE64.add fluxL fluxR) +
    radius (Wasm.IEEE64.mul factor (Wasm.IEEE64.add fluxL fluxR)) +
    value factor * value alpha * radius (Wasm.IEEE64.sub stateR stateL) +
    value factor * radius (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL)) +
    radius (Wasm.IEEE64.mul factor (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL))) + radius output

theorem residual_bound {factor alpha fluxL fluxR stateL stateR output : UInt64}
    (hf : 0 ≤ value factor) (ha : 0 ≤ value alpha)
    (h : Certificate factor alpha fluxL fluxR stateL stateR output) :
    |residual factor alpha fluxL fluxR stateL stateR output| ≤
      errorBound factor alpha fluxL fluxR stateL stateR output := by
  rcases h with ⟨es, em, ej, ev, eh, eo, hvalue, hs, hm, hj, hv, hh, ho⟩
  obtain ⟨hsl, hsu⟩ := abs_le.mp hs
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  obtain ⟨hjl, hju⟩ := abs_le.mp hj
  obtain ⟨hvl, hvu⟩ := abs_le.mp hv
  obtain ⟨hhl, hhu⟩ := abs_le.mp hh
  obtain ⟨hol, hou⟩ := abs_le.mp ho
  have hslo := mul_le_mul_of_nonneg_left hsl hf
  have hshi := mul_le_mul_of_nonneg_left hsu hf
  have hjlo := mul_le_mul_of_nonneg_left hjl (mul_nonneg hf ha)
  have hjhi := mul_le_mul_of_nonneg_left hju (mul_nonneg hf ha)
  have hvlo := mul_le_mul_of_nonneg_left hvl hf
  have hvhi := mul_le_mul_of_nonneg_left hvu hf
  unfold residual errorBound
  rw [hvalue]
  apply abs_le.mpr
  constructor <;> linarith only [hslo, hshi, hml, hmu, hjlo, hjhi, hvlo, hvhi, hhl, hhu, hol, hou]

#print axioms rounded_component
#print axioms residual_bound

end
end Project.ProofKit.F64RusanovResidual
