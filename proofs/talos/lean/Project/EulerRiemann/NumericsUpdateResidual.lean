import Project.EulerCellStep.Safety
import Project.ProofKit.F64ConservativeUpdate

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64ConservativeUpdate
open Project.EulerCellStep.Model (updateCheckedBits)

theorem accepted_update_certificate (ratio state fluxL fluxR : UInt64)
    (h : (updateCheckedBits ratio state fluxL fluxR).status = 0) :
    Certificate ratio state fluxL fluxR (updateCheckedBits ratio state fluxL fluxR).value := by
  unfold updateCheckedBits at h
  split at h
  · rename_i hInput
    dsimp only at h
    split at h
    · rename_i hOutput
      have heq : (updateCheckedBits ratio state fluxL fluxR).value =
          Wasm.IEEE64.sub state (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) := by
        simp [updateCheckedBits, hInput, hOutput]
      rw [heq]
      simp only [Bool.and_eq_true] at hInput hOutput
      obtain ⟨⟨⟨hr, hs⟩, hl⟩, hh⟩ := hInput
      obtain ⟨⟨hd, hp⟩, ho⟩ := hOutput
      exact rounded_update ratio state fluxL fluxR
        (positiveBits_spec ratio hr).1 ((finiteBits_iff state).mp hs)
        ((finiteBits_iff fluxL).mp hl) ((finiteBits_iff fluxR).mp hh)
        ((finiteBits_iff _).mp hd) ((finiteBits_iff _).mp hp) ((finiteBits_iff _).mp ho)
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem accepted_update_residual_bound (ratio state fluxL fluxR : UInt64)
    (h : (updateCheckedBits ratio state fluxL fluxR).status = 0) :
    |residual ratio state fluxL fluxR (updateCheckedBits ratio state fluxL fluxR).value| ≤
      |value ratio| * Project.ProofKit.F64RoundingResidual.radius (Wasm.IEEE64.sub fluxR fluxL) +
      Project.ProofKit.F64RoundingResidual.radius
        (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) +
      Project.ProofKit.F64RoundingResidual.radius (updateCheckedBits ratio state fluxL fluxR).value :=
  residual_bound (accepted_update_certificate ratio state fluxL fluxR h)

#print axioms accepted_update_certificate
#print axioms accepted_update_residual_bound

end Project.EulerRiemann.Numerics
