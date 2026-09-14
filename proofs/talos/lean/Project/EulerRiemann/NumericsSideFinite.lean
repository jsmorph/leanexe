import Project.EulerRiemann.NumericsSafety
import Project.EulerRiemann.NumericsSideValues

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.Euler2DConservative.Model (finiteBits positiveBits)

def SideFinite (rho mx my energy : UInt64) : Prop :=
  let u := Wasm.IEEE64.div mx rho
  let v := Wasm.IEEE64.div my rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my v
  let total := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 total
  let internal := Wasm.IEEE64.sub energy kinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  CodeLib.IEEE64.Finite u ∧ CodeLib.IEEE64.Finite v ∧
    CodeLib.IEEE64.Finite tx ∧ CodeLib.IEEE64.Finite ty ∧
    CodeLib.IEEE64.Finite total ∧ CodeLib.IEEE64.Finite kinetic ∧
    CodeLib.IEEE64.Finite internal ∧ CodeLib.IEEE64.Finite pressure ∧
    CodeLib.IEEE64.Finite (Wasm.IEEE64.add tx pressure) ∧
    CodeLib.IEEE64.Finite (Wasm.IEEE64.mul my u) ∧
    CodeLib.IEEE64.Finite (Wasm.IEEE64.add energy pressure) ∧
    CodeLib.IEEE64.Finite (Wasm.IEEE64.mul u (Wasm.IEEE64.add energy pressure))

theorem accepted_side_finite (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) : SideFinite rho mx my energy := by
  unfold sideCheckedBits at h
  dsimp only at h
  split_ifs at h
  all_goals
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | rename_i hInput hKinetic hPressure hOutput
      simp only [Bool.and_eq_true] at hKinetic hPressure hOutput
      obtain ⟨⟨⟨⟨⟨⟨hu, htx⟩, hv⟩, hty⟩, htotal⟩, hkinetic⟩, hi⟩ := hKinetic
      obtain ⟨⟨hp, _⟩, _⟩ := hPressure
      obtain ⟨⟨⟨⟨⟨_, _⟩, hnormal⟩, htransverse⟩, henthalpy⟩, heflux⟩ := hOutput
      exact ⟨(finiteBits_iff _).mp hu, (finiteBits_iff _).mp hv,
        (finiteBits_iff _).mp htx, (finiteBits_iff _).mp hty,
        (finiteBits_iff _).mp htotal, (finiteBits_iff _).mp hkinetic,
        (positiveBits_spec _ hi).1, (positiveBits_spec _ hp).1,
        (finiteBits_iff _).mp hnormal, (finiteBits_iff _).mp htransverse,
        (finiteBits_iff _).mp henthalpy, (finiteBits_iff _).mp heflux⟩

#print axioms accepted_side_finite
end Project.EulerRiemann.Numerics
