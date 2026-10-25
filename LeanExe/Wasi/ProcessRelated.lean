import LeanExe.Wasi.ProcessRelations
import LeanExe.Wasi.RelatedExec
import LeanExe.Wasi.RelatedPrefix

namespace LeanExe.Wasi

structure ProcessStep.Rel (states : σ → τ → Prop)
    (left : ProcessStep σ) (right : ProcessStep τ) : Prop where
  running : left.running = right.running
  status : left.status = right.status
  state : states left.state right.state

theorem ProcessStep.Rel.symm {states : σ → τ → Prop}
    {left : ProcessStep σ} {right : ProcessStep τ} (related : ProcessStep.Rel states left right) :
    ProcessStep.Rel (fun right left => states left right) right left :=
  ⟨related.running.symm, related.status.symm, related.state⟩

def Process.Rel (states : σ → τ → Prop) (left : Process σ) (right : Process τ) : Prop :=
  ∀ a b, states a b → Action.Rel (ProcessStep.Rel states) (left.step a) (right.step b)

theorem Process.Rel.symm {states : σ → τ → Prop} {left : Process σ} {right : Process τ}
    (related : Process.Rel states left right) : Process.Rel (fun right left => states left right) right left := by
  intro b a state
  exact (related a b state).symm.mono (fun _ _ value => value.symm)

theorem Process.Rel.exec {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : σ} {b : τ} {world trace outcome final}
    (state : states a b) (execution : Process.Exec host left a world trace outcome final) :
    Process.Exec host right b world trace outcome final := by
  induction execution generalizing b with
  | done execution stopped =>
      obtain ⟨result, target, values⟩ := (related _ _ state).exec _ _ _ _ execution
      cases values with
      | returned value =>
          have stoppedExecution := Process.Exec.done target (value.running.symm.trans stopped)
          simpa only [value.status] using stoppedExecution
  | next execution running rest ih =>
      obtain ⟨result, target, values⟩ := (related _ _ state).exec _ _ _ _ execution
      cases values with
      | returned value =>
          exact Process.Exec.next target (value.running.symm.trans running) (ih value.state)
  | exit execution =>
      obtain ⟨result, target, values⟩ := (related _ _ state).exec _ _ _ _ execution
      cases values with
      | exited code => exact Process.Exec.exit target
  | trap execution =>
      obtain ⟨result, target, values⟩ := (related _ _ state).exec _ _ _ _ execution
      cases values with
      | trapped message => exact Process.Exec.trap target

theorem Process.Rel.exec_back {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : σ} {b : τ} {world trace outcome final}
    (state : states a b) (execution : Process.Exec host right b world trace outcome final) :
    Process.Exec host left a world trace outcome final :=
  related.symm.exec state execution

theorem Process.Rel.continue {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : ProcessStep σ} {b : ProcessStep τ} {world trace outcome final}
    (state : ProcessStep.Rel states a b)
    (execution : Process.Continue host left a world trace outcome final) :
    Process.Continue host right b world trace outcome final := by
  cases running : a.running with
  | false =>
      simp only [Process.Continue, ← state.running, running, Bool.false_eq_true, ↓reduceIte]
        at execution ⊢
      simpa only [state.status] using execution
  | true =>
      simp only [Process.Continue, ← state.running, running, ↓reduceIte] at execution ⊢
      exact related.exec state.state execution

theorem Process.Rel.continue_back {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : ProcessStep σ} {b : ProcessStep τ} {world trace outcome final}
    (state : ProcessStep.Rel states a b)
    (execution : Process.Continue host right b world trace outcome final) :
    Process.Continue host left a world trace outcome final :=
  related.symm.continue state.symm execution

theorem Process.Rel.progress {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : ProcessStep σ} {b : ProcessStep τ} {world trace current final}
    (state : ProcessStep.Rel states a b)
    (history : Process.Progress host left a world trace current final) :
    ∃ target, Process.Progress host right b world trace target final ∧
      ProcessStep.Rel states current target := by
  induction history with
  | refl => exact ⟨b, .refl _ _, state⟩
  | next previous running execution ih =>
      obtain ⟨middle, previous, currentState⟩ := ih
      obtain ⟨result, execution, values⟩ :=
        (related _ _ currentState.state).exec _ _ _ _ execution
      cases values with
      | returned value =>
          exact ⟨_, previous.next (currentState.running.symm.trans running) execution, value⟩

theorem Process.Rel.progress_back {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : ProcessStep σ} {b : ProcessStep τ} {world trace current final}
    (state : ProcessStep.Rel states a b)
    (history : Process.Progress host right b world trace current final) :
    ∃ source, Process.Progress host left a world trace source final ∧
      ProcessStep.Rel states source current := by
  obtain ⟨source, history, value⟩ := related.symm.progress state.symm history
  exact ⟨source, history, value.symm⟩

theorem Process.Rel.pending {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : ProcessStep σ} {b : ProcessStep τ} {world trace residual final}
    (state : ProcessStep.Rel states a b)
    (pending : Process.Pending host left a world trace residual final) :
    ∃ target, Process.Pending host right b world trace target final ∧
      Action.Rel (ProcessStep.Rel states) residual target := by
  obtain ⟨before, current, middle, first, history, running, progress, traceEq⟩ := pending
  obtain ⟨next, history, currentState⟩ := related.progress state history
  obtain ⟨target, progress, values⟩ :=
    (related _ _ currentState.state).transportPrefix progress
  exact ⟨target, ⟨before, next, middle, first, history,
    currentState.running.symm.trans running, progress, traceEq⟩, values⟩

theorem Process.Rel.pending_back {World : Type} {host : Host World} {states : σ → τ → Prop}
    {left : Process σ} {right : Process τ} (related : Process.Rel states left right)
    {a : ProcessStep σ} {b : ProcessStep τ} {world trace residual final}
    (state : ProcessStep.Rel states a b)
    (pending : Process.Pending host right b world trace residual final) :
    ∃ source, Process.Pending host left a world trace source final ∧
      Action.Rel (ProcessStep.Rel states) source residual := by
  obtain ⟨source, pending, values⟩ := related.symm.pending state.symm pending
  exact ⟨source, pending, values.symm.mono (fun _ _ value => value.symm)⟩

end LeanExe.Wasi
