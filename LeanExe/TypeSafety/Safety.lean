import LeanExe.TypeSafety.Machine

/-!
# Type safety of the independent core

The binding argument uses typed environments instead of textual substitution:
lookup preserves variable types, and extending the environment implements let
and sum-case binding. Typed continuations record the result type across steps.

The fixed program premise states that every body is typed under its declared
parameter types, using the same global signature table. It does not assume that
any execution is safe, terminates, or returns a result.

The one-step theorem proves both existence and preservation of a successor.
The final theorem covers every finite execution prefix, including open terms
supplied with well-typed environments. It neither assumes nor claims termination.
-/

namespace LeanExe.TypeSafety

variable {program : Program} {signatures : Signatures}

/-- A declared call starts its typed body in precisely its argument environment. -/
theorem enter_call_typed (hprogram : ProgramTyped program signatures)
    (found : lookup signatures function = some ⟨params, result⟩)
    (hargs : EnvTyped arguments params) (hkont : KontTyped signatures kont result τ) :
    ∃ next, enterCall program function arguments kont = some next ∧
      StateTyped signatures next τ := by
  obtain ⟨body, hlookup, hbody⟩ := hprogram.lookup found
  exact ⟨_, by simp [enterCall, hlookup], .eval hbody hargs hkont⟩

/-- Evaluating a typed expression always has a typed successor. -/
theorem eval_step_typed (hprogram : ProgramTyped program signatures)
    (typed : ExprTyped signatures Γ expr α) (henv : EnvTyped env Γ)
    (hkont : KontTyped signatures kont α τ) :
    ∃ next, Step program (.eval expr env kont) next ∧ StateTyped signatures next τ := by
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
  | split hpair hbody =>
      exact ⟨_, rfl, .eval hpair henv (.cons (.splitBody hbody henv) hkont)⟩
  | unitCase hscrutinee hbody =>
      exact ⟨_, rfl, .eval hscrutinee henv (.cons (.unitBody hbody henv) hkont)⟩
  | inl hpayload => exact ⟨_, rfl, .eval hpayload henv (.cons .inl hkont)⟩
  | inr hpayload => exact ⟨_, rfl, .eval hpayload henv (.cons .inr hkont)⟩
  | sumCase hscrutinee hleft hright =>
      exact ⟨_, rfl, .eval hscrutinee henv
        (.cons (.sumBranches hleft hright henv) hkont)⟩
  | add hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.addLeft hright henv) hkont)⟩
  | call found hargs =>
      cases hargs with
      | nil => exact enter_call_typed hprogram found .nil hkont
      | cons harg hrest =>
          exact ⟨_, rfl, .eval harg henv
            (.cons (.callArgs found .nil hrest henv rfl) hkont)⟩
  | arrayEmpty => exact ⟨_, rfl, .ret (ArrayValues.empty_typed _) hkont⟩
  | arraySize harray => exact ⟨_, rfl, .eval harray henv (.cons .arraySize hkont)⟩
  | arrayGet? harray hindex =>
      exact ⟨_, rfl, .eval harray henv (.cons (.arrayGetArray hindex henv) hkont)⟩
  | arraySet? harray hindex hreplacement =>
      exact ⟨_, rfl, .eval harray henv
        (.cons (.arraySetArray hindex hreplacement henv) hkont)⟩
  | arrayPush? harray hvalue =>
      exact ⟨_, rfl, .eval harray henv (.cons (.arrayPushArray hvalue henv) hkont)⟩
  | arrayAppend? hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.arrayAppendLeft hright henv) hkont)⟩

/-- A frame consumes a value of its input type without getting stuck. -/
theorem frame_step_typed (hprogram : ProgramTyped program signatures)
    (hframe : FrameTyped signatures frame α β)
    (hvalue : ValueTyped value α) (hkont : KontTyped signatures kont β τ) :
    ∃ next, Step program (.ret value (frame :: kont)) next ∧ StateTyped signatures next τ := by
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
  | splitBody hbody henv =>
      obtain ⟨left, right, rfl, hleft, hright⟩ := hvalue.prod_canonical
      exact ⟨_, rfl, .eval hbody (.cons hleft (.cons hright henv)) hkont⟩
  | unitBody hbody henv =>
      have same := hvalue.unit_canonical
      cases same
      exact ⟨_, rfl, .eval hbody henv hkont⟩
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

  | callArgs found hdone hremaining henv paramsEqual =>
      have hdone' := hdone.append (EnvTyped.cons hvalue .nil)
      cases hremaining with
      | nil =>
          have hargs : EnvTyped _ _ := hdone'
          rw [paramsEqual] at hargs
          exact enter_call_typed hprogram found hargs hkont
      | cons harg hrest =>
          exact ⟨_, rfl, .eval harg henv
            (.cons (.callArgs found hdone' hrest henv (by
              simpa only [List.append_assoc, List.singleton_append] using paramsEqual)) hkont)⟩
  | arraySize =>
      obtain ⟨elements, rfl, _, bounded⟩ := hvalue.array_canonical
      exact ⟨_, rfl, .ret (.nat bounded) hkont⟩
  | arrayGetArray hindex henv =>
      obtain ⟨elements, rfl, helements, bounded⟩ := hvalue.array_canonical
      exact ⟨_, rfl, .eval hindex henv (.cons (.arrayGetIndex helements bounded) hkont)⟩
  | arrayGetIndex helements _ =>
      obtain ⟨index, rfl, _⟩ := hvalue.nat_canonical
      exact ⟨_, rfl, .ret (ArrayValues.get_typed helements) hkont⟩
  | arraySetArray hindex hreplacement henv =>
      obtain ⟨elements, rfl, helements, bounded⟩ := hvalue.array_canonical
      exact ⟨_, rfl, .eval hindex henv
        (.cons (.arraySetIndex helements bounded hreplacement henv) hkont)⟩
  | arraySetIndex helements bounded hreplacement henv =>
      obtain ⟨index, rfl, indexBounded⟩ := hvalue.nat_canonical
      exact ⟨_, rfl, .eval hreplacement henv
        (.cons (.arraySetValue helements bounded indexBounded) hkont)⟩
  | arraySetValue helements bounded _ =>
      exact ⟨_, rfl, .ret (ArrayValues.set_typed helements bounded hvalue) hkont⟩
  | arrayPushArray hpayload henv =>
      obtain ⟨elements, rfl, helements, bounded⟩ := hvalue.array_canonical
      exact ⟨_, rfl, .eval hpayload henv (.cons (.arrayPushValue helements bounded) hkont)⟩
  | arrayPushValue helements _ =>
      exact ⟨_, rfl, .ret (ArrayValues.push_typed helements hvalue) hkont⟩
  | arrayAppendLeft hright henv =>
      obtain ⟨elements, rfl, helements, bounded⟩ := hvalue.array_canonical
      exact ⟨_, rfl, .eval hright henv (.cons (.arrayAppendRight helements bounded) hkont)⟩
  | arrayAppendRight hleft _ =>
      obtain ⟨elements, rfl, hright, _⟩ := hvalue.array_canonical
      exact ⟨_, rfl, .ret (ArrayValues.append_typed hleft hright) hkont⟩

/-- Every typed state is terminal or takes a type-preserving step. -/
theorem safety_step (hprogram : ProgramTyped program signatures)
    (typed : StateTyped signatures state τ) :
    Terminal state ∨ ∃ next, Step program state next ∧ StateTyped signatures next τ := by
  cases typed with
  | eval hexpr henv hkont => exact .inr (eval_step_typed hprogram hexpr henv hkont)
  | ret hvalue hkont =>
      cases hkont with
      | nil => exact .inl trivial
      | cons hframe hrest => exact .inr (frame_step_typed hprogram hframe hvalue hrest)
  | overflow hleft hright hoverflow => exact .inl ⟨hleft, hright, hoverflow⟩

theorem terminal_no_step (terminal : Terminal state) : step program state = none := by
  cases state with
  | eval expr env kont => exact False.elim terminal
  | ret value kont =>
      cases kont with
      | nil => rfl
      | cons frame rest => exact False.elim terminal
  | overflow left right => rfl

/-- One-step preservation for the independently defined machine. -/
theorem preservation (hprogram : ProgramTyped program signatures)
    (typed : StateTyped signatures state τ) (transition : Step program state next) :
    StateTyped signatures next τ := by
  rcases safety_step hprogram typed with terminal | ⟨next', hstep, htyped⟩
  · have impossible : (none : Option State) = some next :=
      (terminal_no_step (program := program) terminal).symm.trans transition
    cases impossible
  · have same : next' = next := step_deterministic hstep transition
    cases same
    exact htyped

/-- Progress distinguishes permitted overflow from arbitrary stuckness. -/
theorem progress (hprogram : ProgramTyped program signatures)
    (typed : StateTyped signatures state τ) :
    Terminal state ∨ ∃ next, Step program state next := by
  rcases safety_step hprogram typed with terminal | ⟨next, hstep, _⟩
  · exact .inl terminal
  · exact .inr ⟨next, hstep⟩

theorem preservation_steps (hprogram : ProgramTyped program signatures)
    (typed : StateTyped signatures start τ) (execution : Steps program start final) :
    StateTyped signatures final τ := by
  induction execution with
  | refl => exact typed
  | tail history transition ih => exact preservation hprogram ih transition

/-- A stuck state has no successor and is neither a return nor justified overflow. -/
def Stuck (program : Program) (state : State) : Prop := step program state = none ∧ ¬ Terminal state

theorem typed_not_stuck (hprogram : ProgramTyped program signatures)
    (typed : StateTyped signatures state τ) : ¬ Stuck program state := by
  intro stuck
  rcases progress hprogram typed with terminal | ⟨next, transition⟩
  · exact stuck.2 terminal
  · have impossible : (none : Option State) = some next := stuck.1.symm.trans transition
    cases impossible

/-- Type safety for every finite execution prefix from a typed configuration. -/
theorem type_safety (hprogram : ProgramTyped program signatures)
    (typed : StateTyped signatures start τ) (execution : Steps program start final) :
    StateTyped signatures final τ ∧ ¬ Stuck program final := by
  have finalTyped := preservation_steps hprogram typed execution
  exact ⟨finalTyped, typed_not_stuck hprogram finalTyped⟩

/-- Closed source terms inherit the machine theorem through their initial state. -/
theorem closed_type_safety (hprogram : ProgramTyped program signatures)
    (typed : ExprTyped signatures [] expr τ)
    (execution : Steps program (initial expr) final) :
    StateTyped signatures final τ ∧ ¬ Stuck program final :=
  type_safety hprogram (initial_typed typed) execution

/-- Successful executions return a value of the original result type. -/
theorem return_type (hprogram : ProgramTyped program signatures)
    (typed : ExprTyped signatures [] expr τ)
    (execution : Steps program (initial expr) (.ret value [])) : ValueTyped value τ := by
  have finalTyped := preservation_steps hprogram (initial_typed typed) execution
  cases finalTyped with
  | ret hvalue hkont =>
      cases hkont
      exact hvalue

/-- A reached failure proves actual overflow of two represented naturals. -/
theorem overflow_is_justified (hprogram : ProgramTyped program signatures)
    (typed : ExprTyped signatures [] expr τ)
    (execution : Steps program (initial expr) (.overflow left right)) :
    left < nat64Limit ∧ right < nat64Limit ∧ nat64Limit ≤ left + right := by
  have finalTyped := preservation_steps hprogram (initial_typed typed) execution
  cases finalTyped with
  | overflow hleft hright hoverflow => exact ⟨hleft, hright, hoverflow⟩

end LeanExe.TypeSafety
