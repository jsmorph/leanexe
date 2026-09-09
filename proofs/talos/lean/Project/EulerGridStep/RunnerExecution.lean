import Project.EulerGridStep.Runner

namespace Project.EulerGridStep.Runner
open Wasm
open Project.EulerGridStep.Execution

/-- Each call is valid for any host-prepared store satisfying the public arena
    contract. Host copying/reset must reestablish that contract between calls. -/
inductive WasmTrace (m : Wasm.Module) (env : HostEnv Unit) :
    Nat → Array UInt64 → List UInt64 → List (Array UInt64) → Prop
  | nil (cells input) : WasmTrace m env cells input [] []
  | cons {cells input ratio ratios output outputs}
      (call : ∀ (initial : Store Unit) (pointer allocs releases frees : UInt64) (base : Nat),
        GridEntryReady initial pointer input base allocs releases frees →
        TerminatesWith env m 36 initial [.i64 pointer, .i64 ratio]
          (fun final values => ∃ root, values = [.i64 root] ∧
            Project.ProofKit.UInt64Array.At final root output))
      (rest : WasmTrace m env cells (nextGrid cells output) ratios outputs) :
      WasmTrace m env cells input (ratio :: ratios) (output :: outputs)

theorem SafeTrace.wasm {m : Wasm.Module} (hSpec : Spec.ExactSpecFor m)
    (env : HostEnv Unit) {cells input ratios outputs}
    (h : SafeTrace cells input ratios outputs) : WasmTrace m env cells input ratios outputs := by
  induction h with
  | nil input => exact .nil _ input
  | cons heq _ _ _ _ _ ih =>
    refine .cons ?_ ih
    intro initial pointer allocs releases frees base hReady
    rw [heq]
    exact hSpec env initial _ pointer allocs releases frees base _ hReady

noncomputable def RunnerSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (cells : Nat) (ratios : List UInt64) (input : Array UInt64)
    (outputs : List (Array UInt64)), input.size = 3 * cells →
    run ratios input = some outputs →
    SafeTrace cells input ratios outputs ∧ WasmTrace m env cells input ratios outputs

theorem runner_wat_exact_safe : RunnerSpecFor Project.EulerGridStep.«module» := by
  intro env cells ratios input outputs hsize hRun
  have h := run_exact_safe cells ratios input hsize outputs hRun
  exact ⟨h, h.wasm Spec.stepCheckedBits_exact env⟩

/-- Standard stationary Sod data: rho=1/0.125, momentum=0, E=2.5/0.25. -/
def sod100 : Array UInt64 := Array.ofFn (fun j : Fin 300 =>
  if j.val % 3 = 1 then 0
  else if j.val % 3 = 0 then
    if j.val / 3 < 50 then 0x3FF0000000000000 else 0x3FC0000000000000
  else if j.val / 3 < 50 then 0x4004000000000000 else 0x3FD0000000000000)

theorem sod100_wat_exact_safe (env : HostEnv Unit) (ratios : List UInt64)
    (outputs : List (Array UInt64)) (h : run ratios sod100 = some outputs) :
    SafeTrace 100 sod100 ratios outputs ∧
    WasmTrace Project.EulerGridStep.«module» env 100 sod100 ratios outputs :=
  runner_wat_exact_safe env 100 ratios sod100 outputs (by simp [sod100]) h

#print axioms runner_wat_exact_safe
#print axioms sod100_wat_exact_safe
end Project.EulerGridStep.Runner
