import LeanExe.Wasi.NoTrap
import LeanExe.Wasi.Prefix

namespace LeanExe.Wasi

def Host.NoTrapsAt {World : Type} (host : Host World) : Action α → World → Prop
  | .pure _, _ | .loop _ _ _ _ _, _ => True
  | .read capacity _, world =>
      capacity.toNat < 2 ^ 32 →
        ∀ {message committed final}, host.read world capacity (.trapped message committed) final → False
  | .write output bytes _, world =>
      ∀ {message committed final}, host.write world output bytes (.trapped message committed) final → False
  | .exit code, world =>
      ∀ {message final}, host.exitTrap world (exitStatus code) message final → False

def Host.NoTrapsAlong {World : Type} (host : Host World) (action : Action α) (world : World) : Prop :=
  ∀ {trace residual after}, Prefix host action world trace residual after → host.NoTrapsAt residual after

theorem Host.NoTraps.along {World : Type} {host : Host World} (safe : host.NoTraps)
    (action : Action α) (world : World) : host.NoTrapsAlong action world := by
  intro trace residual after progress
  cases residual with
  | pure | loop => trivial
  | read capacity next =>
    intro bound message committed final reply
    exact safe.read reply
  | write output bytes next =>
    intro message committed final reply
    exact safe.write reply
  | exit code =>
    intro message final rejected
    exact safe.exitTrap rejected

theorem Host.NoTrapsAlong.congr {World : Type} {host : Host World} {action other : Action α}
    {world : World} (safe : host.NoTrapsAlong action world) (same : action = other) :
    host.NoTrapsAlong other world := same ▸ safe

theorem Host.NoTrapsAlong.after {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} (safe : host.NoTrapsAlong action world)
    (progress : Prefix host action world trace residual after) : host.NoTrapsAlong residual after := by
  intro rest next final tail
  exact safe (progress.trans tail)

theorem Host.NoTrapsAt.of_bind {World : Type} {host : Host World} {action : Action α}
    {next : α → Action β} {world : World} (safe : host.NoTrapsAt (Action.bind action next) world) :
    host.NoTrapsAt action world := by
  cases action <;> first | trivial | exact safe

theorem Host.NoTrapsAlong.bind_left {World : Type} {host : Host World} {action : Action α}
    {next : α → Action β} {world : World} (safe : host.NoTrapsAlong (Action.bind action next) world) :
    host.NoTrapsAlong action world := by
  intro trace residual after progress
  exact (safe progress.bind).of_bind

theorem Host.NoTrapsAlong.bind_right {World : Type} {host : Host World} {action : Action α}
    {next : α → Action β} {world first value after}
    (safe : host.NoTrapsAlong (Action.bind action next) world)
    (execution : Exec host action world first (.returned value) after) :
    host.NoTrapsAlong (next value) after := by
  intro rest residual final progress
  exact safe (Prefix.bind_after execution progress)

theorem Exec.not_trapped_of_prefix {World : Type} {host : Host World} {action : Action α}
    {world trace outcome final} (execution : Exec host action world trace outcome final) :
    host.NoTrapsAlong action world → ∀ message, outcome ≠ .trapped message := by
  refine Exec.rec
    (motive_1 := fun {α} action world trace outcome final _ =>
      host.NoTrapsAlong action world → ∀ message, outcome ≠ .trapped message)
    (motive_2 := fun {α σ} remaining index (state : σ) test step next world trace outcome final _ =>
      host.NoTrapsAlong (resumeLoop test step next remaining index state) world →
        ∀ message, outcome ≠ .trapped message)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  · intro α world value safe message impossible
    cases impossible
  · intro α capacity next world final trace outcome hCapacity run ih safe
    exact ih (safe.after (.read_reject hCapacity))
  · intro α capacity next world after final trace outcome errno committed hCapacity reply run ih safe
    exact ih (safe.after (.read_return hCapacity reply))
  · intro α capacity next world after message committed hCapacity reply safe
    exact False.elim (safe (.refl _ _) hCapacity reply)
  · intro α output bytes next world after final trace outcome errno committed reply run ih safe
    exact ih (safe.after (.write_return reply))
  · intro α output bytes next world after message committed reply safe
    exact False.elim (safe (.refl _ _) reply)
  · intro α code world final accepted safe message impossible
    cases impossible
  · intro α code world final message rejected safe
    exact False.elim (safe (.refl _ _) rejected)
  · intro σ α count init test step next world final trace outcome run ih safe
    exact ih (safe.after .loop)
  · intro σ α index state test step next world final trace outcome run ih safe
    exact ih safe
  · intro σ α remaining index state test step next world final trace outcome chosen run ih safe
    apply ih
    exact safe.congr (by simp only [resumeLoop, chosen, Bool.false_eq_true, ite_false])
  · intro σ α remaining index state nextState test step next world after final first rest outcome
      chosen stepRun restRun stepIH restIH safe
    have current : host.NoTrapsAlong
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    exact restIH (current.bind_right stepRun)
  · intro σ α remaining index state test step next world final trace code chosen stepRun ih safe message impossible
    cases impossible
  · intro σ α remaining index state test step next world final trace message chosen stepRun ih safe
    have current : host.NoTrapsAlong
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    exact False.elim (ih current.bind_left message rfl)

theorem Exec.returned_or_exited_of_prefix {World : Type} {host : Host World} {action : Action α}
    {world trace outcome final} (execution : Exec host action world trace outcome final)
    (safe : host.NoTrapsAlong action world) :
    (∃ value, outcome = .returned value) ∨ (∃ code, outcome = .exited code) := by
  cases outcome with
  | returned value => exact Or.inl ⟨value, rfl⟩
  | exited code => exact Or.inr ⟨code, rfl⟩
  | trapped message => exact False.elim (execution.not_trapped_of_prefix safe message rfl)

end LeanExe.Wasi
