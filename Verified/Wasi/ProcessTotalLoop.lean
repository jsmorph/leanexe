import Interpreter.Wasm.Wp.Loop

namespace Wasm

theorem wp.with_execution {World : Type} {module : Module} {code : Program}
    {post : Assertion World} {store : Store World} {locals : Locals} {host : HostEnv World}
    (proof : wp module code post store locals host) :
    wp module code
      (fun continuation => post continuation ∧
        ∃ fuel, exec fuel module store locals code host = continuation) store locals host := by
  unfold wp at proof ⊢
  obtain ⟨bound, enough⟩ := proof
  exact ⟨bound, fun fuel more => ⟨enough fuel more, fuel, rfl⟩⟩

def GhostLoopPost (represented : Ghost → Store World → Locals → Prop)
    (relation : Ghost → Ghost → Prop) (ghost : Ghost) (post : Assertion World)
    (values : List Value) : Assertion World
  | .Fallthrough final after => post (.Fallthrough final { after with values })
  | .Break 0 final after =>
      ∃ next, represented next final { after with values } ∧ relation next ghost
  | .Break (index + 1) final after => post (.Break index final after)
  | other => post other

private theorem process_loop_single (fuel : Nat) (module : Module) (host : HostEnv World)
    (store : Store World) (locals : Locals) (body : Program) :
    exec fuel module store locals [.loop 0 0 body [] []] host =
      execOne fuel module store locals (.loop 0 0 body [] []) host := by
  simp only [exec]
  cases execOne fuel module store locals (.loop 0 0 body [] []) host <;> rfl

private theorem process_loop_unfold (fuel : Nat) (module : Module) (host : HostEnv World)
    (store : Store World) (locals : Locals) (body : Program) :
    exec (fuel + 1) module store locals [.loop 0 0 body [] []] host =
      match exec fuel module store locals body host with
      | .Fallthrough final after => .Fallthrough final { after with values := locals.values }
      | .Break 0 final after =>
          execOne fuel module final { after with values := locals.values } (.loop 0 0 body [] []) host
      | .Break (index + 1) final after => .Break index final after
      | other => other := by
  rw [process_loop_single, execOne_loop_succ]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  rfl

theorem wp_loop_ghost {Ghost World : Type} {module : Module} {body : Program}
    {post : Assertion World} {store : Store World} {locals : Locals} {host : HostEnv World}
    (represented : Ghost → Store World → Locals → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    {ghost : Ghost} (initial : represented ghost store locals)
    (step : ∀ ghost store locals, represented ghost store locals →
      wp module body (GhostLoopPost represented relation ghost post locals.values)
        store locals host) :
    wp module [.loop 0 0 body [] []] post store locals host := by
  suffices total : ∀ ghost store locals, represented ghost store locals →
      wp module [.loop 0 0 body [] []] post store locals host from
    total ghost store locals initial
  intro ghost
  induction ghost using wellFounded.induction with
  | h ghost ih =>
      intro store locals rep
      refine wp_of_body_dispatch (step ghost store locals rep) ?_ ?_ ?_ ?_ ?_
      · intro fuel continuation forwarded execution
        cases continuation <;>
          first
          | exact (forwarded : False).elim
          | rw [process_loop_unfold, execution]
      · intro continuation forwarded classification
        cases continuation <;>
          first
          | exact (forwarded : False).elim
          | exact classification
      · intro bound final after classification stable
        refine wp_of_eventually_const (N := bound + 1)
          (cont := .Fallthrough final { after with values := locals.values }) ?_ classification
        intro fuel enough
        obtain ⟨fuel, rfl⟩ : ∃ previous, fuel = previous + 1 := ⟨fuel - 1, by omega⟩
        rw [process_loop_unfold, stable fuel (by omega)]
      · intro bound final after classification stable
        obtain ⟨nextGhost, nextRep, smaller⟩ := classification
        have continued := ih nextGhost smaller final { after with values := locals.values } nextRep
        unfold wp at continued ⊢
        obtain ⟨nextBound, nextExecution⟩ := continued
        refine ⟨max (bound + 1) (nextBound + 1), fun fuel enough => ?_⟩
        obtain ⟨fuel, rfl⟩ : ∃ previous, fuel = previous + 1 := ⟨fuel - 1, by omega⟩
        rw [process_loop_unfold, stable fuel (by omega)]
        simp only
        rw [← process_loop_single]
        exact nextExecution fuel (by omega)
      · intro bound index final after classification stable
        refine wp_of_eventually_const (N := bound + 1) (cont := .Break index final after)
          ?_ classification
        intro fuel enough
        obtain ⟨fuel, rfl⟩ : ∃ previous, fuel = previous + 1 := ⟨fuel - 1, by omega⟩
        rw [process_loop_unfold, stable fuel (by omega)]

end Wasm
