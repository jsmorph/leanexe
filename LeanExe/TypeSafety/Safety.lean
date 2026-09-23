import LeanExe.TypeSafety.Machine

/-!
# Type safety of the independent core

The binding argument uses typed environments instead of textual substitution:
lookup preserves variable types, and extending the environment implements let
and sum-case binding. Typed continuations record the result type across steps.

The one-step theorem proves both existence and preservation of a successor.
The final theorem covers every finite execution prefix, including open terms
supplied with well-typed environments. It neither assumes nor claims termination.
-/

namespace LeanExe.TypeSafety

/-- Evaluating a typed expression always has a typed successor. -/
theorem eval_step_typed (typed : ExprTyped Γ expr α) (henv : EnvTyped env Γ)
    (hkont : KontTyped kont α τ) :
    ∃ next, Step (.eval expr env kont) next ∧ StateTyped next τ := by
  cases typed with
  | var found =>
      obtain ⟨value, hlookup, hvalue⟩ := henv.lookup found
      exact ⟨_, by simp [Step, step, hlookup], .ret hvalue hkont⟩
  | unit => exact ⟨_, rfl, .ret .unit hkont⟩
  | bool => exact ⟨_, rfl, .ret .bool hkont⟩
  | nat bounded => exact ⟨_, rfl, .ret (.nat bounded) hkont⟩
  | letE hbound hbody =>
      exact ⟨_, rfl, .eval hbound henv (.cons (.letBody hbody henv) hkont)⟩
  | ifE hcondition hyes hno =>
      exact ⟨_, rfl, .eval hcondition henv (.cons (.ifBranches hyes hno henv) hkont)⟩
  | pair hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.pairLeft hright henv) hkont)⟩
  | fst hpair => exact ⟨_, rfl, .eval hpair henv (.cons .fst hkont)⟩
  | snd hpair => exact ⟨_, rfl, .eval hpair henv (.cons .snd hkont)⟩
  | inl hpayload => exact ⟨_, rfl, .eval hpayload henv (.cons .inl hkont)⟩
  | inr hpayload => exact ⟨_, rfl, .eval hpayload henv (.cons .inr hkont)⟩
  | sumCase hscrutinee hleft hright =>
      exact ⟨_, rfl, .eval hscrutinee henv
        (.cons (.sumBranches hleft hright henv) hkont)⟩
  | add hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.addLeft hright henv) hkont)⟩

/-- A frame consumes a value of its input type without getting stuck. -/
theorem frame_step_typed (hframe : FrameTyped frame α β)
    (hvalue : ValueTyped value α) (hkont : KontTyped kont β τ) :
    ∃ next, Step (.ret value (frame :: kont)) next ∧ StateTyped next τ := by
  cases hframe with
  | letBody hbody henv =>
      exact ⟨_, rfl, .eval hbody (.cons hvalue henv) hkont⟩
  | ifBranches hyes hno henv =>
      obtain ⟨b, rfl⟩ := hvalue.bool_canonical
      cases b with
      | false => exact ⟨_, rfl, .eval hno henv hkont⟩
      | true => exact ⟨_, rfl, .eval hyes henv hkont⟩
  | pairLeft hright henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.pairRight hvalue) hkont)⟩
  | pairRight hleft =>
      exact ⟨_, rfl, .ret (.pair hleft hvalue) hkont⟩
  | fst =>
      obtain ⟨left, right, rfl, hleft, _⟩ := hvalue.prod_canonical
      exact ⟨_, rfl, .ret hleft hkont⟩
  | snd =>
      obtain ⟨left, right, rfl, _, hright⟩ := hvalue.prod_canonical
      exact ⟨_, rfl, .ret hright hkont⟩
  | inl => exact ⟨_, rfl, .ret (.inl hvalue) hkont⟩
  | inr => exact ⟨_, rfl, .ret (.inr hvalue) hkont⟩
  | sumBranches hleft hright henv =>
      rcases hvalue.sum_canonical with ⟨payload, rfl, hpayload⟩ |
        ⟨payload, rfl, hpayload⟩
      · exact ⟨_, rfl, .eval hleft (.cons hpayload henv) hkont⟩
      · exact ⟨_, rfl, .eval hright (.cons hpayload henv) hkont⟩
  | addLeft hright henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.addRight hvalue) hkont)⟩
  | addRight hleft =>
      obtain ⟨left, rfl, hleftBound⟩ := hleft.nat_canonical
      obtain ⟨right, rfl, hrightBound⟩ := hvalue.nat_canonical
      by_cases bounded : left + right < nat64Limit
      · exact ⟨_, by simp [Step, step, bounded], .ret (.nat bounded) hkont⟩
      · exact ⟨_, by simp [Step, step, bounded],
          .overflow hleftBound hrightBound (Nat.le_of_not_lt bounded)⟩

/-- Every typed state is terminal or takes a type-preserving step. -/
theorem safety_step (typed : StateTyped state τ) :
    Terminal state ∨ ∃ next, Step state next ∧ StateTyped next τ := by
  cases typed with
  | eval hexpr henv hkont => exact .inr (eval_step_typed hexpr henv hkont)
  | ret hvalue hkont =>
      cases hkont with
      | nil => exact .inl trivial
      | cons hframe hrest => exact .inr (frame_step_typed hframe hvalue hrest)
  | overflow hleft hright hoverflow => exact .inl ⟨hleft, hright, hoverflow⟩

theorem terminal_no_step (terminal : Terminal state) : step state = none := by
  cases state with
  | eval expr env kont => exact False.elim terminal
  | ret value kont =>
      cases kont with
      | nil => rfl
      | cons frame rest => exact False.elim terminal
  | overflow left right => rfl

/-- One-step preservation for the independently defined machine. -/
theorem preservation (typed : StateTyped state τ) (transition : Step state next) :
    StateTyped next τ := by
  rcases safety_step typed with terminal | ⟨next', hstep, htyped⟩
  · have impossible : (none : Option State) = some next :=
      (terminal_no_step terminal).symm.trans transition
    cases impossible
  · have same : next' = next := step_deterministic hstep transition
    cases same
    exact htyped

/-- Progress distinguishes permitted overflow from arbitrary stuckness. -/
theorem progress (typed : StateTyped state τ) :
    Terminal state ∨ ∃ next, Step state next := by
  rcases safety_step typed with terminal | ⟨next, hstep, _⟩
  · exact .inl terminal
  · exact .inr ⟨next, hstep⟩

theorem preservation_steps (typed : StateTyped start τ) (execution : Steps start final) :
    StateTyped final τ := by
  induction execution with
  | refl => exact typed
  | tail history transition ih => exact preservation ih transition

/-- A stuck state has no successor and is neither a return nor justified overflow. -/
def Stuck (state : State) : Prop := step state = none ∧ ¬ Terminal state

theorem typed_not_stuck (typed : StateTyped state τ) : ¬ Stuck state := by
  intro stuck
  rcases progress typed with terminal | ⟨next, transition⟩
  · exact stuck.2 terminal
  · have impossible : (none : Option State) = some next := stuck.1.symm.trans transition
    cases impossible

/-- Type safety for every finite execution prefix from a typed configuration. -/
theorem type_safety (typed : StateTyped start τ) (execution : Steps start final) :
    StateTyped final τ ∧ ¬ Stuck final := by
  have finalTyped := preservation_steps typed execution
  exact ⟨finalTyped, typed_not_stuck finalTyped⟩

/-- Closed source terms inherit the machine theorem through their initial state. -/
theorem closed_type_safety (typed : ExprTyped [] expr τ)
    (execution : Steps (initial expr) final) :
    StateTyped final τ ∧ ¬ Stuck final :=
  type_safety (initial_typed typed) execution

/-- Successful executions return a value of the original result type. -/
theorem return_type (typed : ExprTyped [] expr τ)
    (execution : Steps (initial expr) (.ret value [])) : ValueTyped value τ := by
  have finalTyped := preservation_steps (initial_typed typed) execution
  cases finalTyped with
  | ret hvalue hkont =>
      cases hkont
      exact hvalue

/-- A reached failure proves actual overflow of two represented naturals. -/
theorem overflow_is_justified (typed : ExprTyped [] expr τ)
    (execution : Steps (initial expr) (.overflow left right)) :
    left < nat64Limit ∧ right < nat64Limit ∧ nat64Limit ≤ left + right := by
  have finalTyped := preservation_steps (initial_typed typed) execution
  cases finalTyped with
  | overflow hleft hright hoverflow => exact ⟨hleft, hright, hoverflow⟩

end LeanExe.TypeSafety
