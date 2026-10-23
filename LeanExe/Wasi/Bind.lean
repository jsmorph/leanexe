import LeanExe.Wasi.Semantics

namespace LeanExe.Wasi

def Sequenced {World : Type} (host : Host World) (action : Action α) (next : α → Action β)
    (world : World) (trace : List Event) (outcome : Outcome β) (final : World) : Prop :=
  ∃ after first middle rest,
    Exec host action world first middle after ∧ Continue host next after middle rest outcome final ∧
      trace = first ++ rest

theorem LoopExec.unbind {World : Type} {host : Host World} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α} {continuation : α → Action β}
    (hNext : ∀ state world trace outcome final,
      Exec host (Action.bind (next state) continuation) world trace outcome final →
        Sequenced host (next state) continuation world trace outcome final)
    (remaining : Nat) : ∀ {index state world trace outcome final},
      LoopExec host remaining index state test step
        (fun value => Action.bind (next value) continuation) world trace outcome final →
      ∃ after first middle rest,
        LoopExec host remaining index state test step next world first middle after ∧
          Continue host continuation after middle rest outcome final ∧ trace = first ++ rest := by
  induction remaining with
  | zero =>
    intro index state world trace outcome final hRun
    cases hRun with
    | zero hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ :=
        hNext _ _ _ _ _ hRun
      exact ⟨after, first, middle, rest, .zero hFirst, hRest, hTrace⟩
  | succ remaining ih =>
    intro index state world trace outcome final hRun
    cases hRun with
    | stop hTest hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ :=
        hNext _ _ _ _ _ hRun
      exact ⟨after, first, middle, rest, .stop hTest hFirst, hRest, hTrace⟩
    | next hTest hStep hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ := ih hRun
      exact ⟨after, _ ++ first, middle, rest, .next hTest hStep hFirst, hRest,
        by rw [hTrace, List.append_assoc]⟩
    | exit hTest hStep =>
      exact ⟨_, _, .exited _, [], .exit hTest hStep, ⟨rfl, rfl, rfl⟩,
        (List.append_nil _).symm⟩
    | trap hTest hStep =>
      exact ⟨_, _, .trapped _, [], .trap hTest hStep, ⟨rfl, rfl, rfl⟩,
        (List.append_nil _).symm⟩

theorem Exec.unbind {World : Type} {host : Host World} (action : Action α) :
    ∀ {β : Type} {next : α → Action β} {world trace outcome final},
      Exec host (Action.bind action next) world trace outcome final →
        Sequenced host action next world trace outcome final := by
  induction action with
  | pure value =>
    intro β next world trace outcome final hRun
    exact ⟨world, [], .returned value, trace, .pure world value, hRun, rfl⟩
  | read capacity continuation ih =>
    intro β next world trace outcome final hRun
    cases hRun with
    | read_reject hCapacity hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ := ih _ hRun
      exact ⟨after, first, middle, rest, .read_reject hCapacity hFirst, hRest, hTrace⟩
    | read_return hCapacity hHost hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ := ih _ hRun
      exact ⟨after, _ :: first, middle, rest, .read_return hCapacity hHost hFirst, hRest,
        by rw [hTrace]; rfl⟩
    | read_trap hCapacity hHost =>
      exact ⟨_, _, .trapped _, [], .read_trap hCapacity hHost, ⟨rfl, rfl, rfl⟩,
        (List.append_nil _).symm⟩
  | write output bytes continuation ih =>
    intro β next world trace outcome final hRun
    cases hRun with
    | write_return hHost hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ := ih _ hRun
      exact ⟨after, _ :: first, middle, rest, .write_return hHost hFirst, hRest,
        by rw [hTrace]; rfl⟩
    | write_trap hHost =>
      exact ⟨_, _, .trapped _, [], .write_trap hHost, ⟨rfl, rfl, rfl⟩,
        (List.append_nil _).symm⟩
  | exit code =>
    intro β next world trace outcome final hRun
    cases hRun with
    | exit hHost =>
      exact ⟨_, _, .exited _, [], .exit hHost, ⟨rfl, rfl, rfl⟩,
        (List.append_nil _).symm⟩
    | exitTrap hHost =>
      exact ⟨_, _, .trapped _, [], .exitTrap hHost, ⟨rfl, rfl, rfl⟩,
        (List.append_nil _).symm⟩
  | loop count state test step continuation _ ih =>
    intro β next world trace outcome final hRun
    cases hRun with
    | loop hRun =>
      obtain ⟨after, first, middle, rest, hFirst, hRest, hTrace⟩ :=
        LoopExec.unbind (fun state _ _ _ _ h => ih state h) count.toNat hRun
      exact ⟨after, first, middle, rest, .loop hFirst, hRest, hTrace⟩

theorem Exec.bind_iff {World : Type} {host : Host World} {action : Action α}
    {next : α → Action β} {world trace outcome final} :
    Exec host (Action.bind action next) world trace outcome final ↔
      Sequenced host action next world trace outcome final := by
  constructor
  · exact Exec.unbind action
  · rintro ⟨after, first, middle, rest, hFirst, hRest, rfl⟩
    exact hFirst.bind hRest

end LeanExe.Wasi
