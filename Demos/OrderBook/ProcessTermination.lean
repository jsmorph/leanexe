import Demos.OrderBook.ProcessControl
import Demos.OrderBook.ProcessProof
import Verified.Wasi.ProcessTotalCorrect

/-! The termination of the compiled process.  A control ghost pairs the native step result with the
host's ghost, and its rank orders the running flag before the rank of `ProcessControl`.
`control_step_replies` states that a compiled step from a represented running state returns a
represented state of lower rank, and `target_terminates` applies `compiled_process_total_run`: the
module exits with status 0 or 28 when the host makes progress, each step keeps an invariant that
`StepAdvances` names, and the charges of `begin` and of every reached step bound their typed
resource prefixes and fit the memory with the copies of the state. -/

namespace Demos.OrderBook.Process

open Wasm Verified Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamProgress)

abbrev ControlGhost (Ghost : Type) := ProcessStep State × Ghost

abbrev controlOrder : WellFoundedRelation (Nat × Rank) := Prod.lex Nat.lt_wfRel rankOrder

def controlRank (unread zeroWrites : Ghost → Nat) (ghost : ControlGhost Ghost) : Nat × Rank :=
  (if ghost.1.running then 1 else 0, rank unread zeroWrites ghost.1.state ghost.2)

def ControlLt (unread zeroWrites : Ghost → Nat) : ControlGhost Ghost → ControlGhost Ghost → Prop :=
  InvImage controlOrder.rel (controlRank unread zeroWrites)

theorem control_wellFounded (unread zeroWrites : Ghost → Nat) :
    WellFounded (ControlLt unread zeroWrites) :=
  InvImage.wf (controlRank unread zeroWrites) controlOrder.wf

/-- The ghost's native state is related to the compiled state, safe, and represented with the
world, its status is accepted when it stops, and `Inv` holds of it and its ghost while it runs. -/
def ControlRep (rep : Ghost → World → Prop) (Inv : State → Ghost → Prop)
    (ghost : ControlGhost Ghost) (current : ProcessStep stateTy.denote) (world : World) : Prop :=
  ProcessStep.Rel (fun native flat => flat = sourceState native) ghost.1 current ∧
    Safe ghost.1.state ∧ rep ghost.2 world ∧
    (ghost.1.running = false → ghost.1.status = 0 ∨ ghost.1.status = 28) ∧
    (ghost.1.running = true → Inv ghost.1.state ghost.2)

/-- Each step from a safe state where `Inv` holds returns a state whose ghost is represented with
the final world and, while the process runs, satisfies `Inv` at a lower rank. -/
def StepAdvances {World Ghost : Type} (host : Host World) (rep : Ghost → World → Prop)
    (unread zeroWrites : Ghost → Nat) (Inv : State → Ghost → Prop) : Prop :=
  ∀ {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State}, Safe s → Inv s ghost → rep ghost world →
    LeanExe.Wasi.Exec host (step s) world trace (.returned next) final →
    ∃ nextGhost, rep nextGhost final ∧
      (next.running = true → Inv next.state nextGhost ∧
        RankLt (rank unread zeroWrites next.state nextGhost) (rank unread zeroWrites s ghost))

theorem control_begin_replies {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {Inv : State → Ghost → Prop} {ghost : Ghost} {world : World}
    (ready : rep ghost world) (initialInv : Inv initial ghost) {trace outcome final}
    (execution : LeanExe.Wasi.Exec host (entry.beginAction (io.program.funs io.pure.funs))
      world trace outcome final) :
    ∃ current, outcome = .returned current ∧
      ControlRep rep Inv (⟨true, 0, initial⟩, ghost) current final := by
  obtain ⟨nativeOutcome, nativeExecution, related⟩ := begin_related.exec_back execution
  change LeanExe.Wasi.Exec host (.pure ⟨true, 0, initial⟩) world trace nativeOutcome final
    at nativeExecution
  cases nativeExecution
  cases related with
  | returned related =>
      exact ⟨_, rfl, related, Safe.initial, ready, fun impossible => Bool.noConfusion impossible,
        fun _ => initialInv⟩

/-- A step from a represented running state returns a represented state of lower rank, and the
native step from the ghost's state returns the ghost's next state. -/
theorem control_step_replies {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {unread zeroWrites : Ghost → Nat} {Inv : State → Ghost → Prop}
    (progress : StreamProgress host rep unread zeroWrites)
    (advances : StepAdvances host rep unread zeroWrites Inv)
    {ghost : ControlGhost Ghost} {current : ProcessStep stateTy.denote}
    {world : World} (held : ControlRep rep Inv ghost current world)
    (running : current.running = true)
    {trace outcome final}
    (execution : LeanExe.Wasi.Exec host (entry.action (io.program.funs io.pure.funs) current.state)
      world trace outcome final) :
    ∃ nextGhost next, outcome = .returned next ∧ ControlRep rep Inv nextGhost next final ∧
      ControlLt unread zeroWrites nextGhost ghost ∧
      LeanExe.Wasi.Exec host (step ghost.1.state) world trace (.returned nextGhost.1) final := by
  obtain ⟨related, safe, ready, _, invariant⟩ := held
  have beforeRunning : ghost.1.running = true := related.running.trans running
  obtain ⟨nativeOutcome, nativeExecution, resultRelated⟩ :=
    (step_related ghost.1.state current.state related.state).exec_back execution
  obtain ⟨nativeNext, same⟩ := step_returned progress ready safe nativeExecution
  cases same
  cases resultRelated with
  | returned nextRelated =>
      obtain ⟨_, _, nextSafe, status, _⟩ := step_advances progress ready safe nativeExecution
      obtain ⟨nextGhost, nextRep, after⟩ :=
        advances safe (invariant beforeRunning) ready nativeExecution
      refine ⟨(nativeNext, nextGhost), _, rfl,
        ⟨nextRelated, nextSafe, nextRep, status, fun nextRunning => (after nextRunning).1⟩, ?_,
        nativeExecution⟩
      change controlOrder.rel (controlRank unread zeroWrites (nativeNext, nextGhost))
        (controlRank unread zeroWrites ghost)
      cases afterRunning : nativeNext.running with
      | false =>
          simp only [controlRank, afterRunning, beforeRunning, ↓reduceIte]
          exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)
      | true =>
          simp only [controlRank, afterRunning, beforeRunning, ↓reduceIte]
          exact Prod.Lex.right _ (after afterRunning).2

theorem control_exit_accepted {World Ghost : Type} {host : Host World}
    {rep : Ghost → Observed World → Prop} {Inv : State → Ghost → Prop}
    (accepted : ∀ ghost world, rep ghost world → ∀ status,
      status = 0 ∨ status = 28 → ∀ message final,
      (observedHost host).exitTrap world (exitStatus status) message final → False)
    {ghost : ControlGhost Ghost} {current : ProcessStep stateTy.denote}
    {world : Observed World} (held : ControlRep rep Inv ghost current world)
    (stopped : current.running = false) {message final}
    (rejected : (observedHost host).exitTrap world (exitStatus current.status) message final) :
    False := by
  obtain ⟨related, _, ready, status, _⟩ := held
  have nativeStopped := related.running.trans stopped
  exact accepted ghost.2 world ready current.status
    (by simpa only [← related.status] using status nativeStopped) message final rejected

def TargetTerminated {World : Type} (host : Host World) : Result (Observed World) → Prop
  | .Trap final message => message = exitTrap ∧
      ∃ status before, (status = 0 ∨ status = 28) ∧
        (observedHost host).exit before (exitStatus status) final.host
  | _ => False

/-- The compiled process exits with an accepted status 0 or 28 when the host makes progress,
`begin` and every reached step have prefix bounds `beginCharge` and `charge`, and the room
conditions hold for them and the copies of the states.  The conditions on a step need hold only
at states where the invariant `Inv`, which each step keeps, holds with the ghost. -/
theorem target_terminates {World Ghost : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : Ghost → Observed World → Prop) (unread zeroWrites : Ghost → Nat)
    (progress : StreamProgress (observedHost host) rep unread zeroWrites)
    (Inv : State → Ghost → Prop)
    (advances : StepAdvances (observedHost host) rep unread zeroWrites Inv)
    {ghost : Ghost} (ready : rep ghost initial.host)
    (initialInv : Inv Demos.OrderBook.Process.initial ghost)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (charge : ProcessStep State → Ghost → Nat) (beginCharge : Nat)
    (beginRoom : heap.top.toNat + beginCharge +
        stateTy.copyCost (sourceState Demos.OrderBook.Process.initial) ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (beginBounded : Resource.CallPrefixBound (observedHost host)
      (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.begin 0 .nil
      initial.host beginCharge)
    (stepBounded : ∀ (native : ProcessStep State) ghost (world : Observed World),
      Safe native.state → rep ghost world → native.running = true → Inv native.state ghost →
      heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native ghost ≤
          65536 * (PureTransport.erase initial).memoryCap io.pure.module 0 ∧
        Resource.CallPrefixBound (observedHost host)
          (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.step 0
          (.cons (sourceState native.state) .nil) world (charge native ghost))
    (stepRoom : ∀ (native : ProcessStep State) ghost (world : Observed World),
      Safe native.state → rep ghost world → native.running = true → Inv native.state ghost →
      ∀ trace next final nextGhost,
      LeanExe.Wasi.Exec (observedHost host) (step native.state) world trace (.returned next) final →
      rep nextGhost final →
      heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native ghost +
          stateTy.copyCost (sourceState next.state) ≤
        65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ∀ ghost world, rep ghost world → ∀ status,
      status = 0 ∨ status = 28 → ∀ message final,
      (observedHost host).exitTrap world (exitStatus status) message final → False) :
    ∃ bound, ∀ fuel ≥ bound,
      TargetTerminated host (run fuel module startIndex initial [] targetHost) ∧
      ProcessEntryRunResult (observedHost host) begin process initial.host
        (run fuel module startIndex initial [] targetHost) := by
  obtain ⟨bound, allFuel⟩ := compiled_process_total_run io.program entry io.literalPool calls
    (compileWith_runtime io.pure.program io.pure.tables io.pure.wrappers io.literalPool)
    io.profile compactable compactForm compactClosed (ControlRep rep Inv)
    (ControlLt unread zeroWrites)
    (control_wellFounded unread zeroWrites) (fun ghost _ => charge ghost.1 ghost.2) beginCharge
    valid at_ free static io.pool_apart cap
    { beginRoom := by omega
      beginBounded := beginBounded
      beginReplies := fun _ _ _ execution => by
        obtain ⟨current, same, held⟩ := control_begin_replies ready initialInv execution
        refine ⟨_, current, same, held, ?_⟩
        rw [held.1.state]
        exact beginRoom
      stepRoom := fun ghost current world held running => by
        obtain ⟨related, safe, ready, _, invariant⟩ := held
        have nativeRunning := related.running.trans running
        rw [related.state]
        exact (stepBounded ghost.1 ghost.2 world safe ready nativeRunning
          (invariant nativeRunning)).1
      stepBounded := fun ghost current world held running => by
        obtain ⟨related, safe, ready, _, invariant⟩ := held
        have nativeRunning := related.running.trans running
        rw [related.state]
        exact (stepBounded ghost.1 ghost.2 world safe ready nativeRunning
          (invariant nativeRunning)).2
      stepReplies := fun ghost current world held running trace outcome final execution => by
        obtain ⟨nextGhost, next, same, nextHeld, smaller, nativeExecution⟩ :=
          control_step_replies progress advances held running execution
        refine ⟨nextGhost, next, same, nextHeld, smaller, ?_⟩
        obtain ⟨related, safe, ready, _, invariant⟩ := held
        have nativeRunning := related.running.trans running
        rw [related.state, nextHeld.1.state]
        exact stepRoom ghost.1 ghost.2 world safe ready nativeRunning (invariant nativeRunning)
          trace nextGhost.1 final nextGhost.2 nativeExecution nextHeld.2.2.1 }
    (fun _ _ _ held stopped _ _ rejected => control_exit_accepted accepted held stopped rejected)
  refine ⟨bound, fun fuel enough => ?_⟩
  have total : ProcessTotalRunExited host stateTy (ControlRep rep Inv)
      (run fuel module startIndex initial [] targetHost) := allFuel fuel enough
  have completed : run fuel module startIndex initial [] targetHost ≠ .OutOfFuel := by
    intro same
    rw [same] at total
    exact total
  refine ⟨?_, implements host targetHost initial heap fuel valid at_ free static cap completed⟩
  generalize execution : run fuel module startIndex initial [] targetHost = result at total ⊢
  cases result with
  | Trap final message =>
      obtain ⟨messageEq, ghost, current, before, held, stopped, exited⟩ := total
      obtain ⟨related, _, _, status, _⟩ := held
      exact ⟨messageEq, current.status, before,
        by simpa only [← related.status] using status (related.running.trans stopped), exited⟩
  | _ => exact total.elim

end Demos.OrderBook.Process
