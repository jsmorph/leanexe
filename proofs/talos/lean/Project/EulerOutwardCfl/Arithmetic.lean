import Project.EulerOutwardCfl.Program
import Project.EulerOutwardSpeed.Kinetic

namespace Project.EulerOutwardCfl.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Outward (div mul)

def arithmeticDomain (index : Nat) : Prop :=
  index = 4 ∨ index = 5 ∨ index = 6 ∨ 19 ≤ index ∧ index ≤ 25

def arithmeticRename (index : Nat) : Nat :=
  if index ≤ 6 then if index = 4 then 11 else index - 5
  else if index ≤ 24 then index - 17 else 12

theorem arithmeticShift :
    Shift Project.EulerOutwardSpeed.«module» Project.EulerOutwardCfl.«module»
      arithmeticRename arithmeticRename arithmeticDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hlo : 4 ≤ index := by rcases hi with rfl | rfl | rfl | h <;> omega
  have hhi : index ≤ 25 := by rcases hi with rfl | rfl | rfl | h <;> omega
  interval_cases index
  all_goals norm_num [arithmeticDomain] at hi
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [arithmeticDomain]

theorem div_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 7 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = checkedValues (div up a b)) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 24 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.div_exact env initial up a b)

theorem mul_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 12 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = checkedValues (mul up a b)) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 25 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.mul_exact env initial up a b)

theorem positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 11 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 4 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.positive_exact env initial word)

theorem rejected_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 5 initial []
      (fun final values => final = initial ∧ values = [.i64 0, .i64 1]) :=
  Project.FunctionRegion.terminatesWith arithmeticShift 22 (by norm_num [arithmeticDomain])
    (Project.EulerOutwardSpeed.Execution.rejected_exact env initial)

#print axioms arithmeticShift
#print axioms div_exact
#print axioms mul_exact
#print axioms positive_exact
#print axioms rejected_exact
end Project.EulerOutwardCfl.Execution
