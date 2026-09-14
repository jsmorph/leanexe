import Project.EulerOutwardCfl.Arithmetic
import Project.EulerRiemann.ExecutionSpacing
import Project.EulerRiemann.OutwardMesh

namespace Project.EulerOutwardCfl.Execution
open Wasm Project.FunctionRegion
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.EulerRiemann
open Project.EulerRiemann.OutwardCfl (spacingLower)

theorem smallNaturalShift :
    Shift Project.EulerRiemann.«module» Project.EulerOutwardCfl.«module»
      (fun _ => 8) (fun _ => 8) (fun index => index = 33) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  subst index
  refine ⟨_, rfl, rfl, ?_⟩
  prove_portable

theorem smallNatural_exact (env : HostEnv Unit) (initial : Store Unit) (n : Nat) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 8 initial [.i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.smallNaturalBits n)]) :=
  Project.FunctionRegion.terminatesWith smallNaturalShift 33 rfl
    (Project.EulerRiemann.Execution.smallNaturalBits_exact env initial n hn)

theorem spacing_exact (env : HostEnv Unit) (initial : Store Unit) (n : Nat) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 9 initial [.i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = checkedValues (spacingLower n)) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardCfl.«module» func9 _ initial
    (func9Def.toLocals [.i64 (UInt64.ofNat n)]) env
  unfold func9
  wp_run [func9Def]
  guard_call (smallNatural_exact env initial n hn)
  outward_call (div_exact env initial false 0x3FF0000000000000 (Time.smallNaturalBits n))
  simp [spacingLower, checkedValues]

#print axioms smallNaturalShift
#print axioms smallNatural_exact
#print axioms spacing_exact
end Project.EulerOutwardCfl.Execution
