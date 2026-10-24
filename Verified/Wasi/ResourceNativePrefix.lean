import LeanExe.Wasi.PrefixProgress

namespace Verified.Wasi.Resource

open LeanExe.Wasi

theorem advance_bind_cases {World : Type} {host : Host World} {action : Action α}
    {next : α → Action β} {world trace residual after}
    (advance : PrefixAdvance host (Action.bind action next) world trace residual after) :
    (∃ middle, PrefixAdvance host action world trace middle after ∧ residual = Action.bind middle next) ∨
      (∃ value, action = .pure value ∧ PrefixAdvance host (next value) world trace residual after) := by
  cases action with
  | pure value => exact Or.inr ⟨value, rfl, advance⟩
  | read capacity continuation =>
    cases advance with
    | read_reject bound => exact Or.inl ⟨_, .read_reject bound, rfl⟩
    | read_return bound reply => exact Or.inl ⟨_, .read_return bound reply, rfl⟩
  | write output bytes continuation =>
    cases advance with
    | write_return reply => exact Or.inl ⟨_, .write_return reply, rfl⟩
  | exit code => cases advance
  | loop count state test step continuation =>
    cases advance
    exact Or.inl ⟨_, .loop, (resumeLoop_bind test step continuation next _ _ state).symm⟩

theorem exec_of_pure {World : Type} {host : Host World} {action : Action α}
    {value : α} (world : World) (pure : action = .pure value) :
    Exec host action world [] (.returned value) world := by
  rw [pure]
  exact .pure _ _

theorem prefix_pure_exec {World : Type} {host : Host World} {action : Action α}
    {world trace value after} (progress : Prefix host action world trace (.pure value) after) :
    Exec host action world trace (.returned value) after := by
  simpa only [List.append_nil] using progress.complete (.pure after value)

end Verified.Wasi.Resource
