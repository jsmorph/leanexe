import Project.F64SqrtBits.Program
import CodeLib.IEEE64.Operations
import Interpreter.Wasm.Wp.Tactic

/-!
# Raw binary64 sqrt intrinsic

The theorem uses the pure Talos IEEE64 operation.  The native Lean Float body
and host numerical comparisons are executable regression oracles.  The
numerical premises below state the existing Talos theorem's exact domain.
-/
namespace Project.F64SqrtBits.Spec
open Wasm

def sqrtBitsModel (value : UInt64) : UInt64 := Wasm.IEEE64.sqrt value

noncomputable def RealErrorResult (value : UInt64) (result : UInt64) : Prop :=
  CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result - (Real.sqrt (CodeLib.IEEE64.value value))| ≤
      CodeLib.IEEE64.squareRootEpsilon

@[spec_of "lean" "LeanExe.Examples.Float64Bits.sqrtBits"]
noncomputable def SqrtBitsSourceSpec : Prop :=
  ∀ (value : UInt64),
    CodeLib.IEEE64.Finite value → Wasm.IEEE64.scaledMagnitude value ≠ 0 →
    Wasm.IEEE64.sign value = false → Wasm.IEEE64.scaledMagnitude value ≤ 2 ^ 1074 →
    RealErrorResult value (sqrtBitsModel value)

@[proves Project.F64SqrtBits.Spec.SqrtBitsSourceSpec]
theorem sqrtBits_source_real_error : SqrtBitsSourceSpec := by
  intro value h1 h2 h3 h4
  exact CodeLib.IEEE64.sqrt_real_error value h1 h2 h3 h4

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (value : UInt64),
    TerminatesWith env m 0 initial [.i64 value]
      (fun final values =>
        final = initial ∧ values = [.i64 (sqrtBitsModel value)])

noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (value : UInt64),
    CodeLib.IEEE64.Finite value → Wasm.IEEE64.scaledMagnitude value ≠ 0 →
    Wasm.IEEE64.sign value = false → Wasm.IEEE64.scaledMagnitude value ≤ 2 ^ 1074 →
    TerminatesWith env m 0 initial [.i64 value]
      (fun final values =>
        final = initial ∧ values = [.i64 (sqrtBitsModel value)] ∧
          RealErrorResult value (sqrtBitsModel value))

theorem sqrtBits_exact : ExactSpecFor Project.F64SqrtBits.«module» := by
  intro env initial value
  apply TerminatesWith.of_wp_entry_for (f := Project.F64SqrtBits.func0Def)
  · simp [Project.F64SqrtBits.«module»]
  · change wp Project.F64SqrtBits.«module» Project.F64SqrtBits.func0 _ initial
      { params := [.i64 value],
        locals := [.i64 0], values := [] } env
    unfold Project.F64SqrtBits.func0
    wp_run
    simp [sqrtBitsModel, Wasm.f64Sqrt, Project.F64SqrtBits.func0Def]

theorem sqrtBits_wat_real_error :
    RealErrorSpecFor Project.F64SqrtBits.«module» := by
  intro env initial value h1 h2 h3 h4
  refine TerminatesWith.mono (sqrtBits_exact env initial value) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, sqrtBits_source_real_error value h1 h2 h3 h4⟩

#print axioms sqrtBits_source_real_error
#print axioms sqrtBits_exact
#print axioms sqrtBits_wat_real_error
end Project.F64SqrtBits.Spec
