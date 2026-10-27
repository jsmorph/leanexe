import Demos.RunningSum.TerminationTyped

namespace Demos.RunningSum.Termination

open Wasm Verified Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

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
    (initialInv : Inv Demos.RunningSum.initial ghost)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (charge : ProcessStep State → Ghost → Nat) (beginCharge : Nat)
    (beginRoom : heap.top.toNat + beginCharge +
        stateTy.copyCost (sourceState Demos.RunningSum.initial) ≤
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

end Demos.RunningSum.Termination
