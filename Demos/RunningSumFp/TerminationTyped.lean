import Demos.RunningSumFp.Proof
import Demos.RunningSumFp.Termination
import Verified.Wasi.ProcessTotalCorrect

namespace Demos.RunningSumFp.Termination

open Wasm Verified Verified.Wasi LeanExe.Wasi

abbrev ControlGhost (Ghost : Type) := ProcessStep State × Ghost

abbrev controlOrder : WellFoundedRelation (Nat × Rank) := Prod.lex Nat.lt_wfRel rankOrder

def controlRank (unread zeroWrites : Ghost → Nat) (ghost : ControlGhost Ghost) : Nat × Rank :=
  (if ghost.1.running then 1 else 0, rank unread zeroWrites ghost.1.state ghost.2)

def ControlLt (unread zeroWrites : Ghost → Nat) : ControlGhost Ghost → ControlGhost Ghost → Prop :=
  InvImage controlOrder.rel (controlRank unread zeroWrites)

theorem control_wellFounded (unread zeroWrites : Ghost → Nat) :
    WellFounded (ControlLt unread zeroWrites) :=
  InvImage.wf (controlRank unread zeroWrites) controlOrder.wf

def ControlRep (rep : Ghost → World → Prop) (ghost : ControlGhost Ghost)
    (current : ProcessStep stateTy.denote) (world : World) : Prop :=
  ProcessStep.Rel (fun native flat => flat = sourceState native) ghost.1 current ∧
    Safe ghost.1.state ∧ rep ghost.2 world ∧
    (ghost.1.running = false → ghost.1.status = 0 ∨ ghost.1.status = 28)

theorem control_begin_replies {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {ghost : Ghost} {world : World} (ready : rep ghost world)
    {trace outcome final}
    (execution : LeanExe.Wasi.Exec host (entry.beginAction (io.program.funs io.pure.funs))
      world trace outcome final) :
    ∃ current, outcome = .returned current ∧
      ControlRep rep (⟨true, 0, initial⟩, ghost) current final := by
  obtain ⟨nativeOutcome, nativeExecution, related⟩ := begin_related.exec_back execution
  change LeanExe.Wasi.Exec host (.pure ⟨true, 0, initial⟩) world trace nativeOutcome final
    at nativeExecution
  cases nativeExecution
  cases related with
  | returned related =>
      exact ⟨_, rfl, related, Safe.initial, ready, fun impossible => Bool.noConfusion impossible⟩

theorem control_step_replies {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {unread zeroWrites : Ghost → Nat}
    (progress : StreamProgress host rep unread zeroWrites)
    (potential charge : ProcessStep State → Ghost → Nat)
    (decreases : ∀ (native : ProcessStep State) ghost world, Safe native.state → rep ghost world →
      native.running = true → ∀ trace next final nextGhost,
      LeanExe.Wasi.Exec host (step native.state) world trace (.returned next) final →
      rep nextGhost final → potential next nextGhost + charge native ghost ≤ potential native ghost)
    {ghost : ControlGhost Ghost} {current : ProcessStep stateTy.denote}
    {world : World} (held : ControlRep rep ghost current world) (running : current.running = true)
    {trace outcome final}
    (execution : LeanExe.Wasi.Exec host (entry.action (io.program.funs io.pure.funs) current.state)
      world trace outcome final) :
    ∃ nextGhost next, outcome = .returned next ∧ ControlRep rep nextGhost next final ∧
      ControlLt unread zeroWrites nextGhost ghost ∧
      potential nextGhost.1 nextGhost.2 + charge ghost.1 ghost.2 ≤ potential ghost.1 ghost.2 := by
  obtain ⟨related, safe, ready, _⟩ := held
  obtain ⟨nativeOutcome, nativeExecution, resultRelated⟩ :=
    (step_related ghost.1.state current.state related.state).exec_back execution
  obtain ⟨nativeNext, same⟩ := step_returned progress ready safe nativeExecution
  cases same
  cases resultRelated with
  | returned nextRelated =>
      obtain ⟨nextGhost, nextRep, nextSafe, status, smaller⟩ :=
        step_advances progress ready safe nativeExecution
      have beforeRunning : ghost.1.running = true := related.running.trans running
      refine ⟨(nativeNext, nextGhost), _, rfl, ⟨nextRelated, nextSafe, nextRep, status⟩, ?_,
        decreases ghost.1 ghost.2 world safe ready beforeRunning trace nativeNext final nextGhost
          nativeExecution nextRep⟩
      change controlOrder.rel (controlRank unread zeroWrites (nativeNext, nextGhost))
        (controlRank unread zeroWrites ghost)
      cases afterRunning : nativeNext.running with
      | false =>
          simp only [controlRank, afterRunning, beforeRunning, ↓reduceIte]
          exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)
      | true =>
          simp only [controlRank, afterRunning, beforeRunning, ↓reduceIte]
          exact Prod.Lex.right _ (smaller afterRunning)

theorem control_exit_accepted {World Ghost : Type} {host : Host World}
    {rep : Ghost → Observed World → Prop}
    (accepted : ∀ ghost world, rep ghost world → ∀ status,
      status = 0 ∨ status = 28 → ∀ message final,
      (observedHost host).exitTrap world (exitStatus status) message final → False)
    {ghost : ControlGhost Ghost} {current : ProcessStep stateTy.denote}
    {world : Observed World} (held : ControlRep rep ghost current world)
    (stopped : current.running = false) {message final}
    (rejected : (observedHost host).exitTrap world (exitStatus current.status) message final) : False := by
  obtain ⟨related, _, ready, status⟩ := held
  have nativeStopped := related.running.trans stopped
  exact accepted ghost.2 world ready current.status
    (by simpa only [← related.status] using status nativeStopped) message final rejected

end Demos.RunningSumFp.Termination
