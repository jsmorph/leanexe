import Demos.RunningSumFp.Kernel
import Demos.StreamFold.Host

namespace Demos.RunningSumFp.Termination

open LeanExe LeanExe.Wasi

def Safe (state : State) : Prop := StreamFold.Safe (bufferState state)

theorem Safe.initial : Safe initial := StreamFold.Safe.initial _

abbrev Rank := StreamFold.Rank
abbrev RankLt := StreamFold.RankLt
abbrev rankOrder := StreamFold.rankOrder
abbrev StreamProgress (host : Host World) (rep : Ghost → World → Prop)
    (unread zeroWrites : Ghost → Nat) := StreamFold.StreamProgress host rep unread zeroWrites

def rank (unread zeroWrites : Ghost → Nat) (state : State) (ghost : Ghost) : Rank :=
  StreamFold.rank unread zeroWrites (bufferState state) ghost

theorem step_returned {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {outcome : Outcome (ProcessStep State)} (ready : rep ghost world) (safe : Safe state)
    (execution : LeanExe.Wasi.Exec host (step state) world trace outcome final) :
    ∃ next, outcome = .returned next := by
  obtain ⟨mapped, mappedExecution, related⟩ := (buffer_step_related state).exec _ _ _ _ execution
  obtain ⟨next, same⟩ := StreamFold.step_returned progress ready safe mappedExecution
  cases same
  cases related with
  | returned related => exact ⟨_, rfl⟩

theorem step_advances {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State} (ready : rep ghost world) (safe : Safe state)
    (execution : LeanExe.Wasi.Exec host (step state) world trace (.returned next) final) :
    ∃ nextGhost, rep nextGhost final ∧ Safe next.state ∧
      (next.running = false → next.status = 0 ∨ next.status = 28) ∧
      (next.running = true →
        RankLt (rank unread zeroWrites next.state nextGhost) (rank unread zeroWrites state ghost)) := by
  obtain ⟨mapped, mappedExecution, related⟩ := (buffer_step_related state).exec _ _ _ _ execution
  cases related with
  | returned values =>
      obtain ⟨nextGhost, nextRep, nextSafe, status, smaller⟩ :=
        StreamFold.step_advances kernelSpec progress ready safe mappedExecution
      refine ⟨nextGhost, nextRep, ?_, ?_, ?_⟩
      · simpa only [Safe, values.state] using nextSafe
      · intro stopped
        have classified := status (values.running.symm.trans stopped)
        simpa only [← values.status] using classified
      · intro running
        have decreased := smaller (values.running.symm.trans running)
        simpa only [rank, values.state] using decreased

end Demos.RunningSumFp.Termination
