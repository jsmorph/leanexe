import Project.EulerRiemann.Program
import Project.Euler2DConservative.StateGuard
import Project.FunctionRegion.Exec

namespace Project.EulerRiemann.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def sideScalarDomain (index : Nat) : Prop := index < 4
def sideScalarRename (index : Nat) : Nat := index + 2

theorem sideScalarShift :
    Shift Project.Euler2DConservative.«module» Project.EulerRiemann.«module»
      sideScalarRename sideScalarRename sideScalarDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  unfold sideScalarDomain at hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [sideScalarDomain]

def normalizationDomain (index : Nat) : Prop := index < 3 ∨ (4 ≤ index ∧ index ≤ 9) ∨ index = 12
def normalizationRename (index : Nat) : Nat :=
  if index < 3 then index + 6 else if index < 8 then index + 5
  else if index < 10 then index + 7 else 21

theorem normalizationShift :
    Shift Project.Euler2DConservative.«module» Project.EulerRiemann.«module»
      normalizationRename normalizationRename normalizationDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with hi | ⟨hlo, hhi⟩ | rfl
  all_goals try interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [normalizationDomain]

theorem side_positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 2 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith sideScalarShift 0 (by norm_num [sideScalarDomain])
    (Project.Euler2DConservative.Execution.positiveBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

theorem side_abs_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 3 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (Project.Euler2DConservative.Model.absBits word)]) :=
  Project.FunctionRegion.terminatesWith sideScalarShift 1 (by norm_num [sideScalarDomain])
    (Project.Euler2DConservative.Execution.absBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

theorem side_finite_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 4 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.finiteBits word))]) :=
  Project.FunctionRegion.terminatesWith sideScalarShift 2 (by norm_num [sideScalarDomain])
    (Project.Euler2DConservative.Execution.finiteBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

theorem narrow_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 5 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.narrowStateGuard rho mx my energy))]) :=
  Project.FunctionRegion.terminatesWith sideScalarShift 3 (by norm_num [sideScalarDomain])
    (Project.Euler2DConservative.Execution.narrowStateGuard_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial rho mx my energy)

theorem guard_positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 6 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 0 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.positiveBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

theorem guard_finite_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 8 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.finiteBits word))]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 2 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.finiteBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

theorem exponent_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 10 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64Normalize.exponentBits word)]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 5 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.exponentBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

theorem top_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 11 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64Admissibility.topExponent rho mx my energy)]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 6 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.topExponent_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial rho mx my energy)

theorem normalizable_exact (env : HostEnv Unit) (initial : Store Unit) (word top : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 12 initial [.i64 top, .i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Admissibility.normalizable word top))]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 7 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.normalizable_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word top)

theorem residual_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 15 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64InternalEnergy.residual rho mx my energy)]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 8 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.energyResidual_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial rho mx my energy)

theorem normalized_exact (env : HostEnv Unit) (initial : Store Unit) (word top : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 16 initial [.i64 top, .i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64Normalize.normalizedMagnitude word top)]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 9 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.normalizedMagnitude_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word top)

theorem rejected_side_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 21 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) :=
  Project.FunctionRegion.terminatesWith normalizationShift 12 (by norm_num [normalizationDomain])
    (Project.Euler2DConservative.Execution.rejectedSide_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial)

#print axioms sideScalarShift
#print axioms normalizationShift
#print axioms side_positive_exact
#print axioms side_abs_exact
#print axioms side_finite_exact
#print axioms narrow_exact
#print axioms guard_positive_exact
#print axioms guard_finite_exact
#print axioms exponent_exact
#print axioms top_exact
#print axioms normalizable_exact
#print axioms residual_exact
#print axioms normalized_exact
#print axioms rejected_side_exact
end Project.EulerRiemann.Execution
