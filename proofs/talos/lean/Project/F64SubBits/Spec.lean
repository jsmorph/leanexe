import Project.F64SubBits.Program
import CodeLib.IEEE64.Operations
import Interpreter.Wasm.Wp.Tactic

/-!
# Raw binary64 sub intrinsic

The theorem uses the pure Talos IEEE64 operation.  The native Lean Float body
and host numerical comparisons are executable regression oracles.  The
numerical premises below state the existing Talos theorem's exact domain.
-/
namespace Project.F64SubBits.Spec
open Wasm

def subBitsModel (left right : UInt64) : UInt64 := Wasm.IEEE64.sub left right

noncomputable def RealErrorResult (left right : UInt64) (result : UInt64) : Prop :=
  CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result - (CodeLib.IEEE64.value left - CodeLib.IEEE64.value right)| ≤
      CodeLib.IEEE64.arithmeticEpsilon

@[spec_of "lean" "LeanExe.Examples.Float64Bits.subBits"]
noncomputable def SubBitsSourceSpec : Prop :=
  ∀ (left right : UInt64),
    CodeLib.IEEE64.Finite left → CodeLib.IEEE64.Finite right →
    |CodeLib.IEEE64.value left| ≤ 1 → |CodeLib.IEEE64.value right| ≤ 1 →
    RealErrorResult left right (subBitsModel left right)

@[proves Project.F64SubBits.Spec.SubBitsSourceSpec]
theorem subBits_source_real_error : SubBitsSourceSpec := by
  intro left right h1 h2 h3 h4
  exact CodeLib.IEEE64.sub_real_error left right h1 h2 h3 h4

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64),
    TerminatesWith env m 0 initial [.i64 right, .i64 left]
      (fun final values =>
        final = initial ∧ values = [.i64 (subBitsModel left right)])

noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64),
    CodeLib.IEEE64.Finite left → CodeLib.IEEE64.Finite right →
    |CodeLib.IEEE64.value left| ≤ 1 → |CodeLib.IEEE64.value right| ≤ 1 →
    TerminatesWith env m 0 initial [.i64 right, .i64 left]
      (fun final values =>
        final = initial ∧ values = [.i64 (subBitsModel left right)] ∧
          RealErrorResult left right (subBitsModel left right))

theorem subBits_exact : ExactSpecFor Project.F64SubBits.«module» := by
  intro env initial left right
  apply TerminatesWith.of_wp_entry_for (f := Project.F64SubBits.func0Def)
  · simp [Project.F64SubBits.«module»]
  · change wp Project.F64SubBits.«module» Project.F64SubBits.func0 _ initial
      { params := [.i64 left, .i64 right],
        locals := [.i64 0], values := [] } env
    unfold Project.F64SubBits.func0
    wp_run
    simp [subBitsModel, Wasm.f64Sub, Project.F64SubBits.func0Def]

theorem subBits_wat_real_error :
    RealErrorSpecFor Project.F64SubBits.«module» := by
  intro env initial left right h1 h2 h3 h4
  refine TerminatesWith.mono (subBits_exact env initial left right) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, subBits_source_real_error left right h1 h2 h3 h4⟩

#print axioms subBits_source_real_error
#print axioms subBits_exact
#print axioms subBits_wat_real_error
end Project.F64SubBits.Spec
