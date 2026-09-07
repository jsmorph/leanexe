import Project.F64DivBits.Program
import CodeLib.IEEE64.Operations
import Interpreter.Wasm.Wp.Tactic

/-!
# Raw binary64 div intrinsic

The theorem uses the pure Talos IEEE64 operation.  The native Lean Float body
and host numerical comparisons are executable regression oracles.  The
numerical premises below state the existing Talos theorem's exact domain.
-/
namespace Project.F64DivBits.Spec
open Wasm

def divBitsModel (left right : UInt64) : UInt64 := Wasm.IEEE64.div left right

noncomputable def RealErrorResult (left right : UInt64) (result : UInt64) : Prop :=
  CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result - (CodeLib.IEEE64.value left / CodeLib.IEEE64.value right)| ≤
      CodeLib.IEEE64.divisionEpsilon

@[spec_of "lean" "LeanExe.Examples.Float64Bits.divBits"]
noncomputable def DivBitsSourceSpec : Prop :=
  ∀ (left right : UInt64),
    CodeLib.IEEE64.Finite left → CodeLib.IEEE64.Finite right →
    Wasm.IEEE64.scaledMagnitude right ≠ 0 →
    Wasm.IEEE64.scaledMagnitude left ≤ Wasm.IEEE64.scaledMagnitude right →
    RealErrorResult left right (divBitsModel left right)

@[proves Project.F64DivBits.Spec.DivBitsSourceSpec]
theorem divBits_source_real_error : DivBitsSourceSpec := by
  intro left right h1 h2 h3 h4
  exact CodeLib.IEEE64.div_real_error left right h1 h2 h3 h4

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64),
    TerminatesWith env m 0 initial [.i64 right, .i64 left]
      (fun final values =>
        final = initial ∧ values = [.i64 (divBitsModel left right)])

noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64),
    CodeLib.IEEE64.Finite left → CodeLib.IEEE64.Finite right →
    Wasm.IEEE64.scaledMagnitude right ≠ 0 →
    Wasm.IEEE64.scaledMagnitude left ≤ Wasm.IEEE64.scaledMagnitude right →
    TerminatesWith env m 0 initial [.i64 right, .i64 left]
      (fun final values =>
        final = initial ∧ values = [.i64 (divBitsModel left right)] ∧
          RealErrorResult left right (divBitsModel left right))

theorem divBits_exact : ExactSpecFor Project.F64DivBits.«module» := by
  intro env initial left right
  apply TerminatesWith.of_wp_entry_for (f := Project.F64DivBits.func0Def)
  · simp [Project.F64DivBits.«module»]
  · change wp Project.F64DivBits.«module» Project.F64DivBits.func0 _ initial
      { params := [.i64 left, .i64 right],
        locals := [.i64 0], values := [] } env
    unfold Project.F64DivBits.func0
    wp_run
    simp [divBitsModel, Wasm.f64Div, Project.F64DivBits.func0Def]

theorem divBits_wat_real_error :
    RealErrorSpecFor Project.F64DivBits.«module» := by
  intro env initial left right h1 h2 h3 h4
  refine TerminatesWith.mono (divBits_exact env initial left right) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, divBits_source_real_error left right h1 h2 h3 h4⟩

#print axioms divBits_source_real_error
#print axioms divBits_exact
#print axioms divBits_wat_real_error
end Project.F64DivBits.Spec
