import LeanExe.Wasi.Semantics

namespace Verified.Wasi

open LeanExe.Wasi

structure Observed (World : Type) where
  world : World
  events : List Event

def observedHost (host : Host World) : Host (Observed World) where
  exited state := host.exited state.world
  read before capacity reply after :=
    host.read before.world capacity reply after.world ∧
      after.events = before.events ++ [.read capacity reply]
  write before output bytes reply after :=
    host.write before.world output bytes reply after.world ∧
      after.events = before.events ++ [.write output bytes reply]
  exit before code after :=
    host.exit before.world code after.world ∧ after.events = before.events ++ [.exit code]
  exitTrap before code message after :=
    host.exitTrap before.world code message after.world ∧
      after.events = before.events ++ [.exitTrap code message]
  read_bound h := host.read_bound h.1
  write_bound h := host.write_bound h.1
  read_exited h := host.read_exited h.1
  write_exited h := host.write_exited h.1
  exit_recorded h := host.exit_recorded h.1
  exitTrap_exited h := host.exitTrap_exited h.1

theorem exec_observed {World : Type} {host : Host World} {action : Action α}
    {initial final : Observed World} {trace : List Event} {outcome : Outcome α}
    (h : Exec (observedHost host) action initial trace outcome final) :
    Exec host action initial.world trace outcome final.world ∧
      final.events = initial.events ++ trace := by
  refine Exec.rec
    (motive_1 := fun {α} action initial trace outcome final _ =>
      Exec host action initial.world trace outcome final.world ∧
        final.events = initial.events ++ trace)
    (motive_2 := fun {α σ} remaining index (state : σ) test step next
      initial trace outcome final _ =>
      LoopExec host remaining index state test step next initial.world trace outcome final.world ∧
        final.events = initial.events ++ trace)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro α world value
    exact ⟨.pure world.world value, (List.append_nil _).symm⟩
  · intro α capacity next world final trace outcome hCapacity _ ih
    exact ⟨.read_reject hCapacity ih.1, ih.2⟩
  · intro α capacity next world after final trace outcome errno committed hCapacity hHost _ ih
    refine ⟨.read_return hCapacity hHost.1 ih.1, ?_⟩
    rw [ih.2, hHost.2, List.append_assoc]
    rfl
  · intro α capacity next world after message committed hCapacity hHost
    exact ⟨.read_trap hCapacity hHost.1, hHost.2⟩
  · intro α output bytes next world after final trace outcome errno committed hHost _ ih
    refine ⟨.write_return hHost.1 ih.1, ?_⟩
    rw [ih.2, hHost.2, List.append_assoc]
    rfl
  · intro α output bytes next world after message committed hHost
    exact ⟨.write_trap hHost.1, hHost.2⟩
  · intro α code world final hHost
    exact ⟨.exit hHost.1, hHost.2⟩
  · intro α code world final message hHost
    exact ⟨.exitTrap hHost.1, hHost.2⟩
  · intro σ α count init test step next world final trace outcome _ ih
    exact ⟨.loop ih.1, ih.2⟩
  · intro σ α index state test step next world final trace outcome _ ih
    exact ⟨.zero ih.1, ih.2⟩
  · intro σ α remaining index state test step next world final trace outcome hTest _ ih
    exact ⟨.stop hTest ih.1, ih.2⟩
  · intro σ α remaining index state state' test step next world after final first rest outcome
      hTest _ _ ihStep ihRest
    refine ⟨.next hTest ihStep.1 ihRest.1, ?_⟩
    rw [ihRest.2, ihStep.2, List.append_assoc]
  · intro σ α remaining index state test step next world final trace code hTest _ ih
    exact ⟨.exit hTest ih.1, ih.2⟩
  · intro σ α remaining index state test step next world final trace message hTest _ ih
    exact ⟨.trap hTest ih.1, ih.2⟩

end Verified.Wasi
