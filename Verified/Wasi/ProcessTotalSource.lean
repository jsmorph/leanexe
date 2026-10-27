import LeanExe.Wasi.Process

namespace LeanExe.Wasi.Process

theorem exec_of_wellFounded {World State Ghost : Type} {host : Host World}
    {process : Process State} (represented : Ghost → State → World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (status : UInt64 → Prop)
    (step : ∀ ghost state world, represented ghost state world →
      ∃ next trace final nextGhost,
        LeanExe.Wasi.Exec host (process.step state) world trace (.returned next) final ∧
        represented nextGhost next.state final ∧
        (next.running = false → status next.status) ∧
        (next.running = true → relation nextGhost ghost))
    {ghost : Ghost} {state : State} {world : World}
    (initial : represented ghost state world) :
    ∃ trace result final finalGhost finalState,
      Exec host process state world trace (.returned result) final ∧ status result ∧
      represented finalGhost finalState final := by
  suffices total : ∀ ghost state world, represented ghost state world →
      ∃ trace result final finalGhost finalState,
        Exec host process state world trace (.returned result) final ∧ status result ∧
        represented finalGhost finalState final from total ghost state world initial
  intro ghost
  induction ghost using wellFounded.induction with
  | h ghost ih =>
      intro state world rep
      obtain ⟨next, first, middle, nextGhost, execution, nextRep, stopped, smaller⟩ :=
        step ghost state world rep
      cases running : next.running with
      | false =>
          exact ⟨first, next.status, middle, nextGhost, next.state,
            Exec.done execution running, stopped running, nextRep⟩
      | true =>
          obtain ⟨rest, result, final, finalGhost, finalState, continued, resultStatus, finalRep⟩ :=
            ih nextGhost (smaller running) next.state middle nextRep
          exact ⟨first ++ rest, result, final, finalGhost, finalState,
            Exec.next execution running continued, resultStatus, finalRep⟩

end LeanExe.Wasi.Process
