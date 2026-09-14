import Project.ProofKit.F64RoundingResidual

namespace Project.ProofKit.F64ConservativeUpdate
open CodeLib.IEEE64
open Project.ProofKit.F64RoundingResidual
noncomputable section

def Certificate (ratio state fluxL fluxR output : UInt64) : Prop :=
  ∃ differenceError productError subtractionError : ℝ,
    value output = value state - value ratio * (value fluxR - value fluxL) -
      value ratio * differenceError - productError + subtractionError ∧
    |differenceError| ≤ radius (Wasm.IEEE64.sub fluxR fluxL) ∧
    |productError| ≤ radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) ∧
    |subtractionError| ≤ radius output

theorem rounded_update (ratio state fluxL fluxR : UInt64)
    (hr : CodeLib.IEEE64.Finite ratio) (hs : CodeLib.IEEE64.Finite state)
    (hl : CodeLib.IEEE64.Finite fluxL) (hh : CodeLib.IEEE64.Finite fluxR)
    (hd : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub fluxR fluxL))
    (hp : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)))
    (ho : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub state
      (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)))) :
    Certificate ratio state fluxL fluxR
      (Wasm.IEEE64.sub state (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL))) := by
  refine ⟨value (Wasm.IEEE64.sub fluxR fluxL) - (value fluxR - value fluxL),
    value (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) -
      value ratio * value (Wasm.IEEE64.sub fluxR fluxL),
    value (Wasm.IEEE64.sub state (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL))) -
      (value state - value (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL))),
    by ring, sub_error _ _ hh hl hd, mul_error _ _ hr hd hp, sub_error _ _ hs hp ho⟩

def residual (ratio state fluxL fluxR output : UInt64) : ℝ :=
  value output - value state + value ratio * (value fluxR - value fluxL)

theorem balance (ratio state fluxL fluxR output : UInt64) :
    value output - value state = value ratio * (value fluxL - value fluxR) +
      residual ratio state fluxL fluxR output := by
  unfold residual
  ring

theorem residual_bound {ratio state fluxL fluxR output : UInt64}
    (h : Certificate ratio state fluxL fluxR output) :
    |residual ratio state fluxL fluxR output| ≤
      |value ratio| * radius (Wasm.IEEE64.sub fluxR fluxL) +
      radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) + radius output := by
  rcases h with ⟨ed, ep, es, hvalue, hd, hp, hs⟩
  have heq : residual ratio state fluxL fluxR output = -value ratio * ed - ep + es := by
    unfold residual
    rw [hvalue]
    ring
  rw [heq]
  calc
    |-value ratio * ed - ep + es| ≤ |-value ratio * ed - ep| + |es| := abs_add_le _ _
    _ ≤ (|-value ratio * ed| + |ep|) + |es| := by
      have hab : |-value ratio * ed - ep| ≤ |-value ratio * ed| + |ep| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-value ratio * ed) (-ep)
      linarith only [hab]
    _ = |value ratio| * |ed| + |ep| + |es| := by rw [abs_mul, abs_neg]
    _ ≤ _ := by gcongr

#print axioms rounded_update
#print axioms balance
#print axioms residual_bound

end
end Project.ProofKit.F64ConservativeUpdate
