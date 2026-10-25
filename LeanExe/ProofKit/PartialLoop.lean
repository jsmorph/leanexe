import LeanExe.ProofKit.Sequencing

namespace Wasm

def pwp (module : Module) (program : Program) (post : Assertion World)
    (store : Store World) (locals : Locals) (host : HostEnv World := {}) : Prop :=
  ∀ fuel, exec fuel module store locals program host ≠ .OutOfFuel →
    post (exec fuel module store locals program host)

theorem wp.pwp {module : Module} {program : Program} {post : Assertion World}
    {store : Store World} {locals : Locals} {host : HostEnv World}
    (execution : wp module program post store locals host) :
    pwp module program post store locals host := by
  unfold wp at execution
  obtain ⟨bound, execution⟩ := execution
  intro fuel completed
  have result := execution (max fuel bound) (Nat.le_max_right _ _)
  rw [exec_fuel_mono (Nat.le_max_left _ _) completed] at result
  exact result

theorem pwp.conseq {module : Module} {program : Program} {post next : Assertion World}
    {store : Store World} {locals : Locals} {host : HostEnv World}
    (implication : post ⇛ next) (execution : pwp module program post store locals host) :
    pwp module program next store locals host :=
  fun fuel completed => implication _ (execution fuel completed)

def PartialThen (host : HostEnv World) (module : Module) (rest : Program)
    (post : Assertion World) : Assertion World
  | .Fallthrough store locals => pwp module rest post store locals host
  | other => post other

theorem pwp_append {module : Module} {first rest : Program} {post : Assertion World}
    {store : Store World} {locals : Locals} {host : HostEnv World}
    (execution : pwp module first (PartialThen host module rest post) store locals host) :
    pwp module (first ++ rest) post store locals host := by
  intro fuel completed
  rw [exec_append_match] at completed ⊢
  cases firstResult : exec fuel module store locals first host with
  | Fallthrough middle after =>
      have next := execution fuel (by simp [firstResult])
      simp only [firstResult, PartialThen] at next completed ⊢
      exact next fuel completed
  | OutOfFuel => simp [firstResult] at completed
  | _ =>
      have result := execution fuel (by simp [firstResult])
      simpa only [firstResult, PartialThen] using result

def PartialLoopPost (invariant : Store World → Locals → Prop) (post : Assertion World)
    (values : List Value) : Assertion World
  | .Fallthrough store locals => post (.Fallthrough store { locals with values })
  | .Break 0 store locals => invariant store { locals with values }
  | .Break (index + 1) store locals => post (.Break index store locals)
  | other => post other

theorem pwp_loop {module : Module} {body : Program} {post : Assertion World}
    {store : Store World} {locals : Locals} {host : HostEnv World}
    (invariant : Store World → Locals → Prop)
    (initial : invariant store locals)
    (step : ∀ store locals, invariant store locals →
      pwp module body (PartialLoopPost invariant post locals.values) store locals host) :
    pwp module [.loop 0 0 body [] []] post store locals host := by
  have single : ∀ fuel store locals,
      exec fuel module store locals [.loop 0 0 body [] []] host =
        execOne fuel module store locals (.loop 0 0 body [] []) host := by
    intro fuel store locals
    simp only [exec]
    cases execOne fuel module store locals (.loop 0 0 body [] []) host <;> rfl
  suffices loop : ∀ fuel store locals, invariant store locals →
      execOne fuel module store locals (.loop 0 0 body [] []) host ≠ .OutOfFuel →
      post (execOne fuel module store locals (.loop 0 0 body [] []) host) by
    intro fuel completed
    rw [single] at completed ⊢
    exact loop fuel store locals initial completed
  intro fuel
  induction fuel with
  | zero =>
      intro store locals _ completed
      simp only [execOne.eq_def] at completed
      exact False.elim (completed rfl)
  | succ fuel ih =>
      intro store locals held completed
      rw [execOne_loop_succ] at completed ⊢
      simp only [List.drop_zero, List.take_zero, List.nil_append] at completed ⊢
      cases result : exec fuel module store locals body host with
      | OutOfFuel => simp only [result] at completed; exact False.elim (completed rfl)
      | Break index next after =>
          have bodyPost := step store locals held fuel (by simp [result])
          rw [result] at bodyPost completed
          cases index with
          | zero => exact ih next _ bodyPost completed
          | succ index => exact bodyPost
      | _ =>
          have bodyPost := step store locals held fuel (by simp [result])
          simpa only [result, PartialLoopPost] using bodyPost

end Wasm
