import Demos.RunningSumFp.TerminationTyped

namespace Demos.RunningSumFp.Termination

open Wasm Verified Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def TargetTerminated {World : Type} (host : Host World) : Result (Observed World) → Prop
  | .Trap final message => message = exitTrap ∧
      ∃ status before, (status = 0 ∨ status = 28) ∧
        (observedHost host).exit before (exitStatus status) final.host
  | _ => False

theorem target_terminates {World Ghost : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : Ghost → Observed World → Prop) (unread zeroWrites : Ghost → Nat)
    (progress : StreamProgress (observedHost host) rep unread zeroWrites)
    {ghost : Ghost} (ready : rep ghost initial.host)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (potential charge : ProcessStep State → Ghost → Nat) (start beginCharge : Nat)
    (beginResources : heap.Within (PureTransport.erase initial) io.pure.module start ∧
      beginCharge ≤ start ∧ Resource.CallPrefixBound (observedHost host)
        (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.begin 0 .nil
        initial.host beginCharge)
    (beginRoom : potential ⟨true, 0, Demos.RunningSumFp.initial⟩ ghost + beginCharge ≤ start)
    (stepResources : ∀ (native : ProcessStep State) ghost (world : Observed World),
      Safe native.state → rep ghost world → native.running = true →
      charge native ghost ≤ potential native ghost ∧
        Resource.CallPrefixBound (observedHost host)
          (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.step 0
          (.cons (sourceState native.state) .nil) world (charge native ghost))
    (decreases : ∀ (native : ProcessStep State) ghost (world : Observed World),
      Safe native.state → rep ghost world → native.running = true → ∀ trace next final nextGhost,
      LeanExe.Wasi.Exec (observedHost host) (step native.state) world trace (.returned next) final →
      rep nextGhost final → potential next nextGhost + charge native ghost ≤ potential native ghost)
    (accepted : ∀ ghost world, rep ghost world → ∀ status,
      status = 0 ∨ status = 28 → ∀ message final,
      (observedHost host).exitTrap world (exitStatus status) message final → False) :
    ∃ bound, ∀ fuel ≥ bound,
      TargetTerminated host (run fuel module startIndex initial [] targetHost) ∧
      ProcessEntryRunResult (observedHost host) begin process initial.host
        (run fuel module startIndex initial [] targetHost) := by
  obtain ⟨bound, allFuel⟩ := compiled_process_total_run io.program entry io.literalPool calls
    (compileWith_runtime io.pure.program io.pure.tables io.pure.wrappers io.literalPool)
    io.profile (Encoding.checkProgramForm_sound (by decide +kernel))
    (by decide +kernel) (ControlRep rep) (ControlLt unread zeroWrites)
    (control_wellFounded unread zeroWrites) (fun ghost _ => potential ghost.1 ghost.2)
    (fun ghost _ => charge ghost.1 ghost.2) start beginCharge valid at_ static io.pool_apart cap
    beginResources
    (fun _ _ _ execution => by
      obtain ⟨current, same, held⟩ := control_begin_replies ready execution
      exact ⟨_, current, same, held, beginRoom⟩)
    (fun ghost current world held running => by
      obtain ⟨related, safe, ready, _⟩ := held
      rw [related.state]
      exact stepResources ghost.1 ghost.2 world safe ready (related.running.trans running))
    (fun _ _ _ held running _ _ _ execution =>
      control_step_replies progress potential charge decreases held running execution)
    (fun _ _ _ held stopped _ _ rejected => control_exit_accepted accepted held stopped rejected)
  refine ⟨bound, fun fuel enough => ?_⟩
  have total : ProcessTotalRunExited host stateTy (ControlRep rep)
      (run fuel module startIndex initial [] targetHost) := allFuel fuel enough
  have completed : run fuel module startIndex initial [] targetHost ≠ .OutOfFuel := by
    intro same
    rw [same] at total
    exact total
  refine ⟨?_, implements host targetHost initial heap fuel valid at_ static cap completed⟩
  generalize execution : run fuel module startIndex initial [] targetHost = result at total ⊢
  cases result with
  | Trap final message =>
      obtain ⟨messageEq, ghost, current, before, held, stopped, exited⟩ := total
      obtain ⟨related, _, _, status⟩ := held
      exact ⟨messageEq, current.status, before,
        by simpa only [← related.status] using status (related.running.trans stopped), exited⟩
  | _ => exact total.elim

end Demos.RunningSumFp.Termination
