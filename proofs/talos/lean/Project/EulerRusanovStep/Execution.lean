import Project.EulerRusanov.Execution
import Project.EulerRusanov.InterfaceData
import Project.EulerRusanovStep.Update
import Interpreter.Wasm.Wp.Call

/-!
# Fuel-independent execution of the fixed Euler--Rusanov step

The exported function at index six makes three calls to the guarded scalar
flux function embedded at index zero.  Once their three status words have
been checked, it makes six calls to the pure quarter-step helper at index two.
This proof composes those nine calls without replacing either generated body
by a source-level evaluator.

All three fixed flux rows are accepted.  Their exact words come from the
public Euler--Rusanov interface-data model facts, while the final seven words
are stated through the independent pure step model.  Every callee preserves
the complete store, so the no-argument exported entry does as well.
-/

namespace Project.EulerRusanovStep.Spec

open Wasm

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000

/-- The scalar guarded flux proof is reusable at function zero of the larger
step module because that generated function body is definitionally identical
to the standalone compiler case and the module has no imports. -/
theorem func0_exact
    (env : HostEnv Unit) (initial : Store Unit)
    (rhoL uL pL rhoR uR pR : UInt64) :
    TerminatesWith env Project.EulerRusanovStep.«module» 0 initial
      [.i64 pR, .i64 uR, .i64 rhoR, .i64 pL, .i64 uL, .i64 rhoL]
      (fun final values =>
        final = initial ∧
          values = Project.EulerRusanov.Model.resultValues
            rhoL uL pL rhoR uR pR) :=
  Project.EulerRusanov.Spec.rusanovFluxCheckedBits_exact_in_module
    (m := Project.EulerRusanovStep.«module») (by rfl) (by rfl)
    env initial rhoL uL pL rhoR uR pR

private theorem sodLL_func0_exact
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRusanovStep.«module» 0 initial
      [.i64 Model.oneBits, .i64 Model.zeroBits, .i64 Model.oneBits,
        .i64 Model.oneBits, .i64 Model.zeroBits, .i64 Model.oneBits]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 Model.sodLLFlux.energy, .i64 Model.sodLLFlux.momentum,
              .i64 Model.sodLLFlux.mass, .i64 Model.sodLLFlux.status]) := by
  simpa only [Model.sodLLFlux, Project.EulerRusanov.Model.resultValues] using
    (func0_exact env initial
      Model.oneBits Model.zeroBits Model.oneBits
      Model.oneBits Model.zeroBits Model.oneBits)

private theorem sodLR_func0_exact
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRusanovStep.«module» 0 initial
      [.i64 Model.tenthBits, .i64 Model.zeroBits, .i64 Model.eighthBits,
        .i64 Model.oneBits, .i64 Model.zeroBits, .i64 Model.oneBits]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 Model.sodLRFlux.energy, .i64 Model.sodLRFlux.momentum,
              .i64 Model.sodLRFlux.mass, .i64 Model.sodLRFlux.status]) := by
  simpa only [Model.sodLRFlux, Project.EulerRusanov.Model.resultValues] using
    (func0_exact env initial
      Model.oneBits Model.zeroBits Model.oneBits
      Model.eighthBits Model.zeroBits Model.tenthBits)

private theorem sodRR_func0_exact
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRusanovStep.«module» 0 initial
      [.i64 Model.tenthBits, .i64 Model.zeroBits, .i64 Model.eighthBits,
        .i64 Model.tenthBits, .i64 Model.zeroBits, .i64 Model.eighthBits]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 Model.sodRRFlux.energy, .i64 Model.sodRRFlux.momentum,
              .i64 Model.sodRRFlux.mass, .i64 Model.sodRRFlux.status]) := by
  simpa only [Model.sodRRFlux, Project.EulerRusanov.Model.resultValues] using
    (func0_exact env initial
      Model.eighthBits Model.zeroBits Model.tenthBits
      Model.eighthBits Model.zeroBits Model.tenthBits)

private theorem sodLLFlux_expected :
    Model.sodLLFlux = Project.EulerRusanov.InterfaceData.sodLL.expected := by
  simpa [Model.sodLLFlux, Model.zeroBits, Model.oneBits,
    Project.EulerRusanov.InterfaceData.modelResult,
    Project.EulerRusanov.InterfaceData.sodLL] using
    Project.EulerRusanov.InterfaceData.sodLL_model

private theorem sodLRFlux_expected :
    Model.sodLRFlux = Project.EulerRusanov.InterfaceData.sodLR.expected := by
  simpa [Model.sodLRFlux, Model.zeroBits, Model.oneBits, Model.eighthBits,
    Model.tenthBits, Project.EulerRusanov.InterfaceData.modelResult,
    Project.EulerRusanov.InterfaceData.sodLR] using
    Project.EulerRusanov.InterfaceData.sodLR_model

private theorem sodRRFlux_expected :
    Model.sodRRFlux = Project.EulerRusanov.InterfaceData.sodRR.expected := by
  simpa [Model.sodRRFlux, Model.zeroBits, Model.eighthBits, Model.tenthBits,
    Project.EulerRusanov.InterfaceData.modelResult,
    Project.EulerRusanov.InterfaceData.sodRR] using
    Project.EulerRusanov.InterfaceData.sodRR_model

private theorem sodLLFlux_status : Model.sodLLFlux.status = 0 := by
  rw [sodLLFlux_expected]
  rfl

private theorem sodLRFlux_status : Model.sodLRFlux.status = 0 := by
  rw [sodLRFlux_expected]
  rfl

private theorem sodRRFlux_status : Model.sodRRFlux.status = 0 := by
  rw [sodRRFlux_expected]
  rfl

/-- Fuel-independent exact behavior of the generated no-argument step entry.
The seven result words are top-first, hence reverse source-structure order. -/
theorem func6_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRusanovStep.«module» 6 initial []
      (fun final values =>
        final = initial ∧ values = Model.resultValues) := by
  apply TerminatesWith.of_wp_entry_for
    (f := Project.EulerRusanovStep.func6Def)
  · simp [Project.EulerRusanovStep.«module»]
  · change wp Project.EulerRusanovStep.«module»
      Project.EulerRusanovStep.func6 _ initial
      (Project.EulerRusanovStep.func6Def.toLocals []) env
    unfold Project.EulerRusanovStep.func6
    wp_run [Project.EulerRusanovStep.func6Def]

    refine wp_call_tw (sodLL_func0_exact env initial) ?_
    rintro stLL valuesLL ⟨hstLL, rfl⟩
    subst stLL
    wp_run

    refine wp_call_tw (sodLR_func0_exact env initial) ?_
    rintro stLR valuesLR ⟨hstLR, rfl⟩
    subst stLR
    wp_run

    refine wp_call_tw (sodRR_func0_exact env initial) ?_
    rintro stRR valuesRR ⟨hstRR, rfl⟩
    subst stRR
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]

    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run [sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]

    refine wp_call_tw (func2_exact env initial
      Model.oneBits Model.sodLLFlux.mass Model.sodLRFlux.mass) ?_
    rintro stLD valuesLD ⟨hstLD, rfl⟩
    subst stLD
    wp_run

    refine wp_call_tw (func2_exact env initial
      Model.zeroBits Model.sodLLFlux.momentum Model.sodLRFlux.momentum) ?_
    rintro stLM valuesLM ⟨hstLM, rfl⟩
    subst stLM
    wp_run

    refine wp_call_tw (func2_exact env initial
      Model.fiveHalvesBits Model.sodLLFlux.energy Model.sodLRFlux.energy) ?_
    rintro stLE valuesLE ⟨hstLE, rfl⟩
    subst stLE
    wp_run

    refine wp_call_tw (func2_exact env initial
      Model.eighthBits Model.sodLRFlux.mass Model.sodRRFlux.mass) ?_
    rintro stRD valuesRD ⟨hstRD, rfl⟩
    subst stRD
    wp_run

    refine wp_call_tw (func2_exact env initial
      Model.zeroBits Model.sodLRFlux.momentum Model.sodRRFlux.momentum) ?_
    rintro stRM valuesRM ⟨hstRM, rfl⟩
    subst stRM
    wp_run

    refine wp_call_tw (func2_exact env initial
      Model.quarterBits Model.sodLRFlux.energy Model.sodRRFlux.energy) ?_
    rintro stRE valuesRE ⟨hstRE, rfl⟩
    subst stRE
    wp_run
    simp [Model.resultValues, Model.sodQuarterStepCheckedBitsModel,
      Model.zeroBits,
      sodLLFlux_status, sodLRFlux_status, sodRRFlux_status]

#print axioms func0_exact
#print axioms func6_exact

end Project.EulerRusanovStep.Spec
