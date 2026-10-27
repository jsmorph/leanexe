import LeanExe.Wasi.Process
import LeanExe.Wasi.Prefix

namespace LeanExe.Wasi.Process

def Continue {World σ : Type} (host : Host World) (process : Process σ)
    (current : ProcessStep σ) (world : World) (trace : List Event)
    (outcome : Outcome UInt64) (final : World) : Prop :=
  if current.running then Exec host process current.state world trace outcome final
  else trace = [] ∧ outcome = .returned current.status ∧ final = world

theorem Continue.step {World σ : Type} {host : Host World} {process : Process σ}
    {current next : ProcessStep σ} {world middle final first rest outcome}
    (running : current.running = true)
    (execution : LeanExe.Wasi.Exec host (process.step current.state)
      world first (.returned next) middle)
    (continuation : Continue host process next middle rest outcome final) :
    Continue host process current world (first ++ rest) outcome final := by
  simp only [Continue, running, ↓reduceIte]
  cases nextRunning : next.running with
  | false =>
      simp only [Continue, nextRunning, Bool.false_eq_true, ↓reduceIte] at continuation
      rcases continuation with ⟨rfl, rfl, rfl⟩
      simpa only [List.append_nil] using Exec.done execution nextRunning
  | true =>
      simp only [Continue, nextRunning, ↓reduceIte] at continuation
      exact Exec.next execution nextRunning continuation

inductive Progress {World σ : Type} (host : Host World) (process : Process σ) :
    ProcessStep σ → World → List Event → ProcessStep σ → World → Prop where
  | refl (current world) : Progress host process current world [] current world
  | next {initial world trace current middle first next final}
      (history : Progress host process initial world trace current middle)
      (running : current.running = true)
      (execution : LeanExe.Wasi.Exec host (process.step current.state)
        middle first (.returned next) final) :
      Progress host process initial world (trace ++ first) next final

theorem Progress.finish {World σ : Type} {host : Host World} {process : Process σ}
    {initial world trace current middle rest outcome final}
    (history : Progress host process initial world trace current middle)
    (continuation : Continue host process current middle rest outcome final) :
    Continue host process initial world (trace ++ rest) outcome final := by
  induction history generalizing rest with
  | refl => exact continuation
  | next _ running execution ih =>
      rw [List.append_assoc]
      exact ih (Continue.step running execution continuation)

theorem Progress.marker {World σ : Type} {host : Host World} {process : Process σ}
    {initial world trace current final}
    (history : Progress host process initial world trace current final) :
    host.exited final = host.exited world := by
  induction history with
  | refl => rfl
  | next _ _ execution ih =>
      exact execution.exited_marker.trans ih

def Pending {World σ : Type} (host : Host World) (process : Process σ)
    (initial : ProcessStep σ) (world : World) (trace : List Event)
    (residual : Action (ProcessStep σ)) (final : World) : Prop :=
  ∃ before current middle first,
    Progress host process initial world before current middle ∧
    current.running = true ∧
    LeanExe.Wasi.Prefix host (process.step current.state) middle first residual final ∧
    trace = before ++ first

theorem Progress.done {World σ : Type} {host : Host World} {process : Process σ}
    {initial world trace current final}
    (history : Progress host process initial world trace current final)
    (stopped : current.running = false) :
    Continue host process initial world trace (.returned current.status) final := by
  have finished : Continue host process current final [] (.returned current.status) final := by
    simp [Continue, stopped]
  simpa only [List.append_nil] using history.finish finished

end LeanExe.Wasi.Process
