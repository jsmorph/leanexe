import Project.EulerDynamicFlux.Safety
import Project.ProofKit.F64RusanovResidual

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64RusanovResidual
open Project.EulerDynamicFlux.Model (componentCheckedBits)

theorem accepted_component_certificate (alpha fluxL fluxR stateL stateR : UInt64)
    (h : (componentCheckedBits alpha fluxL fluxR stateL stateR).status = 0) :
    Certificate 0x3FE0000000000000 alpha fluxL fluxR stateL stateR
      (componentCheckedBits alpha fluxL fluxR stateL stateR).value := by
  unfold componentCheckedBits at h
  split at h
  · rename_i hInput
    dsimp only at h
    split at h
    · rename_i hOutput
      have heq : (componentCheckedBits alpha fluxL fluxR stateL stateR).value =
          Wasm.IEEE64.sub (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add fluxL fluxR))
            (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.mul alpha (Wasm.IEEE64.sub stateR stateL))) := by
        simp [componentCheckedBits, hInput, hOutput]
      rw [heq]
      simp only [Bool.and_eq_true] at hInput hOutput
      obtain ⟨⟨⟨⟨ha, hfl⟩, hfr⟩, hsl⟩, hsr⟩ := hInput
      obtain ⟨⟨⟨⟨⟨hsum, hmean⟩, hjump⟩, hvisc⟩, hhalf⟩, hresult⟩ := hOutput
      exact rounded_component 0x3FE0000000000000 alpha fluxL fluxR stateL stateR
        (by unfold CodeLib.IEEE64.Finite; decide) (positiveBits_spec alpha ha).1
        ((finiteBits_iff _).mp hfl) ((finiteBits_iff _).mp hfr)
        ((finiteBits_iff _).mp hsl) ((finiteBits_iff _).mp hsr)
        ((finiteBits_iff _).mp hsum) ((finiteBits_iff _).mp hmean)
        ((finiteBits_iff _).mp hjump) ((finiteBits_iff _).mp hvisc)
        ((finiteBits_iff _).mp hhalf) ((finiteBits_iff _).mp hresult)
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem accepted_component_alpha (alpha fluxL fluxR stateL stateR : UInt64)
    (h : (componentCheckedBits alpha fluxL fluxR stateL stateR).status = 0) :
    0 < value alpha := by
  unfold componentCheckedBits at h
  split at h
  · rename_i hInput
    simp only [Bool.and_eq_true] at hInput
    exact (positiveBits_spec alpha hInput.1.1.1.1).2
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem accepted_component_residual_bound (alpha fluxL fluxR stateL stateR : UInt64)
    (h : (componentCheckedBits alpha fluxL fluxR stateL stateR).status = 0) :
    |residual 0x3FE0000000000000 alpha fluxL fluxR stateL stateR
      (componentCheckedBits alpha fluxL fluxR stateL stateR).value| ≤
      errorBound 0x3FE0000000000000 alpha fluxL fluxR stateL stateR
        (componentCheckedBits alpha fluxL fluxR stateL stateR).value :=
  residual_bound (positiveBits_spec 0x3FE0000000000000 (by decide)).2.le
    (accepted_component_alpha alpha fluxL fluxR stateL stateR h).le
    (accepted_component_certificate alpha fluxL fluxR stateL stateR h)

#print axioms accepted_component_certificate
#print axioms accepted_component_alpha
#print axioms accepted_component_residual_bound

end Project.EulerRiemann.Numerics
