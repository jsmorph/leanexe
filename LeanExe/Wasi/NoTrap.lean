import LeanExe.Wasi.Semantics

namespace LeanExe.Wasi

structure Host.NoTraps {World : Type} (host : Host World) : Prop where
  read : ∀ {world capacity message committed final},
    host.read world capacity (.trapped message committed) final → False
  write : ∀ {world output bytes message committed final},
    host.write world output bytes (.trapped message committed) final → False
  exitTrap : ∀ {world code message final}, host.exitTrap world code message final → False

theorem Exec.not_trapped {World : Type} {host : Host World} {action : Action α}
    {world trace outcome final} (execution : Exec host action world trace outcome final)
    (safe : host.NoTraps) : ∀ message, outcome ≠ .trapped message := by
  refine Exec.rec
    (motive_1 := fun {α} action world trace outcome final _ =>
      ∀ message, outcome ≠ .trapped message)
    (motive_2 := fun {α σ} remaining index (state : σ) test step next world trace outcome final _ =>
      ∀ message, outcome ≠ .trapped message)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  · intro α world value message impossible
    cases impossible
  · intro α capacity next world final trace outcome hCapacity run ih
    exact ih
  · intro α capacity next world after final trace outcome errno committed hCapacity reply run ih
    exact ih
  · intro α capacity next world after message committed hCapacity reply
    exact False.elim (safe.read reply)
  · intro α output bytes next world after final trace outcome errno committed reply run ih
    exact ih
  · intro α output bytes next world after message committed reply
    exact False.elim (safe.write reply)
  · intro α code world final accepted message impossible
    cases impossible
  · intro α code world final message rejected
    exact False.elim (safe.exitTrap rejected)
  · intro σ α count init test step next world final trace outcome run ih
    exact ih
  · intro σ α index state test step next world final trace outcome run ih
    exact ih
  · intro σ α remaining index state test step next world final trace outcome chosen run ih
    exact ih
  · intro σ α remaining index state nextState test step next world after final first rest outcome
      chosen stepRun restRun stepIH restIH
    exact restIH
  · intro σ α remaining index state test step next world final trace code chosen stepRun ih message impossible
    cases impossible
  · intro σ α remaining index state test step next world final trace message chosen stepRun ih
    exact False.elim (ih message rfl)

theorem Exec.returned_or_exited {World : Type} {host : Host World} {action : Action α}
    {world trace outcome final} (execution : Exec host action world trace outcome final)
    (safe : host.NoTraps) :
    (∃ value, outcome = .returned value) ∨ (∃ code, outcome = .exited code) := by
  cases outcome with
  | returned value => exact Or.inl ⟨value, rfl⟩
  | exited code => exact Or.inr ⟨code, rfl⟩
  | trapped message => exact False.elim (execution.not_trapped safe message rfl)

end LeanExe.Wasi
