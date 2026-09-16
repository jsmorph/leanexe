import Project.EulerCertificateFlux.Program
import Project.EulerOutwardSpeed.Subtraction
import Project.EulerOutwardSpeed.Addition
import Project.EulerOutwardSpeed.Multiplication
import Project.EulerOutwardSpeed.Division

namespace Project.EulerCertificateFlux.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)
open Project.EulerOutwardSpeed.Execution (checkedValues)

def arithmeticDomain (index : Nat) : Prop :=
  index = 4 ∨ index = 5 ∨ index = 6 ∨ (19 ≤ index ∧ index ≤ 28) ∨ index = 30

def arithmeticRename : Nat → Nat
  | 4 => 21
  | 5 => 5
  | 6 => 6
  | 19 => 7
  | 20 => 8
  | 21 => 9
  | 22 => 10
  | 23 => 11
  | 24 => 22
  | 25 => 16
  | 26 => 1
  | 27 => 12
  | 28 => 2
  | 30 => 25
  | index => index

theorem arithmeticShift :
    Shift Project.EulerOutwardSpeed.«module» Project.EulerCertificateFlux.«module»
      arithmeticRename arithmeticRename arithmeticDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with rfl | rfl | rfl | ⟨hlo, hhi⟩ | rfl
  all_goals try interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [arithmeticDomain]

theorem outward_add_exact (env : HostEnv Unit) (initial : Store Unit)
    (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 12 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧
        values = checkedValues (Project.ProofKit.F64Outward.add up a b)) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 27 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.add_exact env initial up a b)

theorem outward_sub_exact (env : HostEnv Unit) (initial : Store Unit)
    (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 25 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧
        values = checkedValues (Project.ProofKit.F64Outward.sub up a b)) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 30 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.sub_exact env initial up a b)

theorem outward_mul_exact (env : HostEnv Unit) (initial : Store Unit)
    (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 16 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧
        values = checkedValues (Project.ProofKit.F64Outward.mul up a b)) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 25 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.mul_exact env initial up a b)

theorem outward_div_exact (env : HostEnv Unit) (initial : Store Unit)
    (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 22 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧
        values = checkedValues (Project.ProofKit.F64Outward.div up a b)) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 24 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.div_exact env initial up a b)

theorem finite_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 6 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.finiteBits word))]) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 6 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.finite_exact env initial word)

theorem positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 21 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 4 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.positive_exact env initial word)

#print axioms arithmeticShift
#print axioms outward_add_exact
#print axioms outward_sub_exact
#print axioms outward_mul_exact
#print axioms outward_div_exact
end Project.EulerCertificateFlux.Execution
