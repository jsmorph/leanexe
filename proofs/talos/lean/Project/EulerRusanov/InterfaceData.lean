import Project.EulerRusanov.ArtifactTranslation
import Project.EulerRusanov.WasmNumerical

/-!
# Verified Euler Rusanov interface data

The eight rows below are the formal counterpart of
`euler-rusanov-interface-v1.csv`.  Every input and output is an exact raw
binary64 word.  The host-side generator is intentionally outside this theorem:
it invokes the frozen WebAssembly once per row and serializes the returned
words, while this module proves those words from the exact artifact semantics.
-/

namespace Project.EulerRusanov.InterfaceData

open Wasm

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-- One frozen raw-word interface row in public source-result order. -/
structure Row where
  name : String
  rhoL : UInt64
  uL : UInt64
  pL : UInt64
  rhoR : UInt64
  uR : UInt64
  pR : UInt64
  expected : Model.CheckedFluxBits
  deriving DecidableEq, Repr

namespace Row

/-- Talos uses a top-first operand stack, hence reverse source argument order. -/
def inputValues (row : Row) : List Wasm.Value :=
  [.i64 row.pR, .i64 row.uR, .i64 row.rhoR,
    .i64 row.pL, .i64 row.uL, .i64 row.rhoL]

/-- Talos return values are likewise top-first, reversing the source fields. -/
def resultValues (row : Row) : List Wasm.Value :=
  [.i64 row.expected.energy, .i64 row.expected.momentum,
    .i64 row.expected.mass, .i64 row.expected.status]

def fluxBits (row : Row) : Model.FluxBits :=
  { mass := row.expected.mass
    momentum := row.expected.momentum
    energy := row.expected.energy }

end Row

def sodLL : Row :=
  { name := "sod_ll"
    rhoL := 0x3FF0000000000000, uL := 0x0000000000000000,
    pL := 0x3FF0000000000000
    rhoR := 0x3FF0000000000000, uR := 0x0000000000000000,
    pR := 0x3FF0000000000000
    expected :=
      { status := 0, mass := 0, momentum := 0x3FF0000000000000,
        energy := 0 } }

def sodRR : Row :=
  { name := "sod_rr"
    rhoL := 0x3FC0000000000000, uL := 0x0000000000000000,
    pL := 0x3FB999999999999A
    rhoR := 0x3FC0000000000000, uR := 0x0000000000000000,
    pR := 0x3FB999999999999A
    expected :=
      { status := 0, mass := 0, momentum := 0x3FB999999999999A,
        energy := 0 } }

def sodLR : Row :=
  { name := "sod_lr"
    rhoL := 0x3FF0000000000000, uL := 0x0000000000000000,
    pL := 0x3FF0000000000000
    rhoR := 0x3FC0000000000000, uR := 0x0000000000000000,
    pR := 0x3FB999999999999A
    expected :=
      { status := 0, mass := 0x3FE8800000000000,
        momentum := 0x3FE199999999999A, energy := 0x3FFF800000000000 } }

def sodRL : Row :=
  { name := "sod_rl"
    rhoL := 0x3FC0000000000000, uL := 0x0000000000000000,
    pL := 0x3FB999999999999A
    rhoR := 0x3FF0000000000000, uR := 0x0000000000000000,
    pR := 0x3FF0000000000000
    expected :=
      { status := 0, mass := 0xBFE8800000000000,
        momentum := 0x3FE199999999999A, energy := 0xBFFF800000000000 } }

def movingConsistency : Row :=
  { name := "moving_consistency"
    rhoL := 0x3FE0000000000000, uL := 0x3FD0000000000000,
    pL := 0x3FD0000000000000
    rhoR := 0x3FE0000000000000, uR := 0x3FD0000000000000,
    pR := 0x3FD0000000000000
    expected :=
      { status := 0, mass := 0x3FC0000000000000,
        momentum := 0x3FD2000000000000, energy := 0x3FCC800000000000 } }

def guardMinToMax : Row :=
  { name := "guard_min_to_max"
    rhoL := 0x3FC0000000000000, uL := 0xBFE0000000000000,
    pL := 0x3FB0000000000000
    rhoR := 0x3FF0000000000000, uR := 0x3FE0000000000000,
    pR := 0x3FF0000000000000
    expected :=
      { status := 0, mass := 0xBFE1800000000000,
        momentum := 0x3FC7000000000000, energy := 0xBFF4C80000000000 } }

def guardMaxToMin : Row :=
  { name := "guard_max_to_min"
    rhoL := 0x3FF0000000000000, uL := 0x3FE0000000000000,
    pL := 0x3FF0000000000000
    rhoR := 0x3FC0000000000000, uR := 0xBFE0000000000000,
    pR := 0x3FB0000000000000
    expected :=
      { status := 0, mass := 0x3FEF800000000000,
        momentum := 0x3FF2A00000000000, energy := 0x4007F40000000000 } }

def nanRejected : Row :=
  { name := "nan_rejected"
    rhoL := 0x7FF8000000000000, uL := 0x0000000000000000,
    pL := 0x3FF0000000000000
    rhoR := 0x3FC0000000000000, uR := 0x0000000000000000,
    pR := 0x3FB999999999999A
    expected := { status := 1, mass := 0, momentum := 0, energy := 0 } }

/-- Stable order of the public version-one interface data. -/
def rows : List Row :=
  [sodLL, sodRR, sodLR, sodRL, movingConsistency,
    guardMinToMax, guardMaxToMin, nanRejected]

def modelResult (row : Row) : Model.CheckedFluxBits :=
  Model.checkedFluxBitsModel
    row.rhoL row.uL row.pL row.rhoR row.uR row.pR

theorem sodLL_model : modelResult sodLL = sodLL.expected := by
  decide

theorem sodRR_model : modelResult sodRR = sodRR.expected := by
  decide

theorem sodLR_model : modelResult sodLR = sodLR.expected := by
  decide

theorem sodRL_model : modelResult sodRL = sodRL.expected := by
  decide

theorem movingConsistency_model :
    modelResult movingConsistency = movingConsistency.expected := by
  decide

theorem guardMinToMax_model :
    modelResult guardMinToMax = guardMinToMax.expected := by
  decide

theorem guardMaxToMin_model :
    modelResult guardMaxToMin = guardMaxToMin.expected := by
  decide

theorem nanRejected_model :
    modelResult nanRejected = nanRejected.expected := by
  decide

theorem sodLL_guard :
    Model.eulerGuard sodLL.rhoL sodLL.uL sodLL.pL
      sodLL.rhoR sodLL.uR sodLL.pR = true := by
  decide

theorem sodRR_guard :
    Model.eulerGuard sodRR.rhoL sodRR.uL sodRR.pL
      sodRR.rhoR sodRR.uR sodRR.pR = true := by
  decide

theorem sodLR_guard :
    Model.eulerGuard sodLR.rhoL sodLR.uL sodLR.pL
      sodLR.rhoR sodLR.uR sodLR.pR = true := by
  decide

theorem sodRL_guard :
    Model.eulerGuard sodRL.rhoL sodRL.uL sodRL.pL
      sodRL.rhoR sodRL.uR sodRL.pR = true := by
  decide

theorem movingConsistency_guard :
    Model.eulerGuard movingConsistency.rhoL movingConsistency.uL
      movingConsistency.pL movingConsistency.rhoR movingConsistency.uR
      movingConsistency.pR = true := by
  decide

theorem guardMinToMax_guard :
    Model.eulerGuard guardMinToMax.rhoL guardMinToMax.uL guardMinToMax.pL
      guardMinToMax.rhoR guardMinToMax.uR guardMinToMax.pR = true := by
  decide

theorem guardMaxToMin_guard :
    Model.eulerGuard guardMaxToMin.rhoL guardMaxToMin.uL guardMaxToMin.pL
      guardMaxToMin.rhoR guardMaxToMin.uR guardMaxToMin.pR = true := by
  decide

theorem nanRejected_guard :
    Model.eulerGuard nanRejected.rhoL nanRejected.uL nanRejected.pL
      nanRejected.rhoR nanRejected.uR nanRejected.pR = false := by
  decide

/-! ## Dataset behavior contract -/

/-- One accepted row has exact generated-Wasm words, preserved store, the
guard-derived state bounds and signal-speed bounds, and the componentwise
real-error theorem for those same three frozen output words. -/
structure AcceptedSpecFor (m : Wasm.Module) (row : Row) : Prop where
  guard : Model.eulerGuard row.rhoL row.uL row.pL
    row.rhoR row.uR row.pR = true
  expectedStatus : row.expected.status = 0
  leftBounds : Bounds.StateBounds row.rhoL row.uL row.pL
  rightBounds : Bounds.StateBounds row.rhoR row.uR row.pR
  leftSignalSpeed :
    |CodeLib.IEEE64.value row.uL| +
        Real.sqrt
          (Model.gammaReal * CodeLib.IEEE64.value row.pL /
            CodeLib.IEEE64.value row.rhoL) ≤ Model.alphaReal
  rightSignalSpeed :
    |CodeLib.IEEE64.value row.uR| +
        Real.sqrt
          (Model.gammaReal * CodeLib.IEEE64.value row.pR /
            CodeLib.IEEE64.value row.rhoR) ≤ Model.alphaReal
  terminates : ∀ (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env m 0 initial row.inputValues
      (fun final values =>
        final = initial ∧
          values = row.resultValues ∧
          Numerical.FluxRealError
            row.rhoL row.uL row.pL row.rhoR row.uR row.pR row.fluxBits)

/-- A rejected row fails the raw-word guard and returns its exact frozen tuple
without changing the WebAssembly store. -/
structure RejectedSpecFor (m : Wasm.Module) (row : Row) : Prop where
  guard : Model.eulerGuard row.rhoL row.uL row.pL
    row.rhoR row.uR row.pR = false
  terminates : ∀ (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env m 0 initial row.inputValues
      (fun final values => final = initial ∧ values = row.resultValues)

/-- Complete behavior promised by version one of the frozen public dataset. -/
structure InterfaceV1SpecFor (m : Wasm.Module) : Prop where
  sodLL : AcceptedSpecFor m sodLL
  sodRR : AcceptedSpecFor m sodRR
  sodLR : AcceptedSpecFor m sodLR
  sodRL : AcceptedSpecFor m sodRL
  movingConsistency : AcceptedSpecFor m movingConsistency
  guardMinToMax : AcceptedSpecFor m guardMinToMax
  guardMaxToMin : AcceptedSpecFor m guardMaxToMin
  nanRejected : RejectedSpecFor m nanRejected

private theorem model_result_values
    (row : Row) (hmodel : modelResult row = row.expected) :
    Model.resultValues row.rhoL row.uL row.pL row.rhoR row.uR row.pR =
      row.resultValues := by
  change Model.checkedFluxBitsModel
      row.rhoL row.uL row.pL row.rhoR row.uR row.pR = row.expected at hmodel
  simp only [Model.resultValues, Row.resultValues]
  rw [hmodel]

private theorem accepted_of_specs
    (m : Wasm.Module) (row : Row)
    (hspec : Spec.RealErrorSpecFor m)
    (hguard : Model.eulerGuard row.rhoL row.uL row.pL
      row.rhoR row.uR row.pR = true)
    (hmodel : modelResult row = row.expected) :
    AcceptedSpecFor m row := by
  have hbounds := Bounds.eulerGuard_spec
    row.rhoL row.uL row.pL row.rhoR row.uR row.pR hguard
  have hnumeric :=
    Numerical.checkedFluxBitsModel_real_error_of_guard hguard
  have hmodel' : Model.checkedFluxBitsModel
      row.rhoL row.uL row.pL row.rhoR row.uR row.pR = row.expected := hmodel
  refine
    { guard := hguard
      expectedStatus := ?_
      leftBounds := hbounds.1
      rightBounds := hbounds.2
      leftSignalSpeed := hbounds.1.signalSpeed_le_alpha
      rightSignalSpeed := hbounds.2.signalSpeed_le_alpha
      terminates := ?_ }
  · rw [← hmodel']
    exact hnumeric.1
  · intro env initial
    refine TerminatesWith.mono
      (hspec env initial row.rhoL row.uL row.pL
        row.rhoR row.uR row.pR hguard) ?_
    rintro final values ⟨hfinal, hvalues, _hstatus, herror⟩
    refine ⟨hfinal, hvalues.trans (model_result_values row hmodel), ?_⟩
    rw [hmodel'] at herror
    simpa only [Row.fluxBits] using herror

private theorem rejected_of_exact
    (m : Wasm.Module) (row : Row)
    (hspec : Spec.ExactSpecFor m)
    (hguard : Model.eulerGuard row.rhoL row.uL row.pL
      row.rhoR row.uR row.pR = false)
    (hmodel : modelResult row = row.expected) :
    RejectedSpecFor m row := by
  refine { guard := hguard, terminates := ?_ }
  intro env initial
  refine TerminatesWith.mono
    (hspec env initial row.rhoL row.uL row.pL
      row.rhoR row.uR row.pR) ?_
  rintro final values ⟨hfinal, hvalues⟩
  exact ⟨hfinal, hvalues.trans (model_result_values row hmodel)⟩

/-- The compiler-generated Talos module realizes all eight exact rows. -/
theorem interfaceV1_generated :
    InterfaceV1SpecFor Project.EulerRusanov.«module» := by
  let hreal := Spec.rusanovFluxCheckedBits_wat_real_error
  let hexact := Spec.rusanovFluxCheckedBits_exact
  exact
    { sodLL := accepted_of_specs _ sodLL hreal sodLL_guard sodLL_model
      sodRR := accepted_of_specs _ sodRR hreal sodRR_guard sodRR_model
      sodLR := accepted_of_specs _ sodLR hreal sodLR_guard sodLR_model
      sodRL := accepted_of_specs _ sodRL hreal sodRL_guard sodRL_model
      movingConsistency := accepted_of_specs _ movingConsistency hreal
        movingConsistency_guard movingConsistency_model
      guardMinToMax := accepted_of_specs _ guardMinToMax hreal
        guardMinToMax_guard guardMinToMax_model
      guardMaxToMin := accepted_of_specs _ guardMaxToMin hreal
        guardMaxToMin_guard guardMaxToMin_model
      nanRejected := rejected_of_exact _ nanRejected hexact
        nanRejected_guard nanRejected_model }

/-- The exact frozen artifact bytes decode and validate to a module realizing
all eight rows, including exact outputs and the accepted numerical facts. -/
theorem artifact_interfaceV1 :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧
      InterfaceV1SpecFor validated.toTalos := by
  apply Artifact.artifact_correct_of InterfaceV1SpecFor
  simpa [Artifact.executionCache] using interfaceV1_generated

#print axioms interfaceV1_generated
#print axioms artifact_interfaceV1

end Project.EulerRusanov.InterfaceData
