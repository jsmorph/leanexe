import LeanExe.TypeSafety.Machine

/-!
# Type safety of the independent core

The binding argument uses typed environments instead of textual substitution:
lookup preserves variable types, and extending the environment implements let,
sum, natural, and constructor-pattern binding. Typed continuations record the
result type across steps.

The fixed program premise requires formed nominal declarations and signatures,
and states that every body is typed under its declared
parameter types, using the same global signature table. It does not assume that
any execution is safe, terminates, or returns a result.

The one-step theorem proves both existence and preservation of a successor.
The final theorem covers every finite execution prefix, including open terms
supplied with well-typed environments. It neither assumes nor claims termination.
-/

namespace LeanExe.TypeSafety

variable {declarations : DataDecls} {program : Program} {signatures : Signatures}

/-- A declared call starts its typed body in precisely its argument environment. -/
theorem enter_call_typed (hprogram : ProgramTyped declarations program signatures)
    (found : lookup signatures function = some ⟨params, result⟩)
    (hargs : EnvTyped declarations arguments params)
    (hkont : KontTyped declarations signatures kont result τ) :
    ∃ next, enterCall program function arguments kont = some next ∧
      StateTyped declarations signatures next τ := by
  obtain ⟨body, hlookup, hbody⟩ := hprogram.bodies.lookup found
  exact ⟨_, by simp [enterCall, hlookup], .eval hbody hargs hkont⟩

/-- Evaluating a typed expression always has a typed successor. -/
theorem eval_step_typed (hprogram : ProgramTyped declarations program signatures)
    (typed : ExprTyped declarations signatures Γ expr α) (henv : EnvTyped declarations env Γ)
    (hkont : KontTyped declarations signatures kont α τ) :
    ∃ next, Step program (.eval expr env kont) next ∧ StateTyped declarations signatures next τ := by
  cases typed with
  | var found =>
      obtain ⟨value, hlookup, hvalue⟩ := henv.lookup found
      exact ⟨_, by simp [Step, step, hlookup], .ret hvalue hkont⟩
  | unit => exact ⟨_, rfl, .ret .unit hkont⟩
  | bool => exact ⟨_, rfl, .ret .bool hkont⟩
  | nat bounded => exact ⟨_, rfl, .ret (.nat bounded) hkont⟩
  | word bounded => exact ⟨_, rfl, .ret (.word bounded) hkont⟩
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
  | inl hpayload other => exact ⟨_, rfl, .eval hpayload henv (.cons (.inl other) hkont)⟩
  | inr hpayload other => exact ⟨_, rfl, .eval hpayload henv (.cons (.inr other) hkont)⟩
  | sumCase hscrutinee hleft hright =>
      exact ⟨_, rfl, .eval hscrutinee henv
        (.cons (.sumBranches hleft hright henv) hkont)⟩
  | natCase hscrutinee hzero hsucc =>
      exact ⟨_, rfl, .eval hscrutinee henv (.cons (.natBranches hzero hsucc henv) hkont)⟩
  | natBin operation hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.natBinLeft operation hright henv) hkont)⟩
  | natCmp operation hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.natCmpLeft operation hright henv) hkont)⟩
  | structEq hleft hright domain =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.structEqLeft hright domain henv) hkont)⟩
  | wordBin width operation hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.wordBinLeft width operation hright henv) hkont)⟩
  | wordCmp width operation hleft hright =>
      exact ⟨_, rfl, .eval hleft henv (.cons (.wordCmpLeft width operation hright henv) hkont)⟩
  | wordOfNat target hvalue =>
      exact ⟨_, rfl, .eval hvalue henv (.cons (.wordOfNat target) hkont)⟩
  | wordToNat source hvalue =>
      exact ⟨_, rfl, .eval hvalue henv (.cons (.wordToNat source) hkont)⟩
  | wordCast source target hvalue =>
      exact ⟨_, rfl, .eval hvalue henv (.cons (.wordCast source target) hkont)⟩
  | call found hargs =>
      cases hargs with
      | nil => exact enter_call_typed hprogram found .nil hkont
      | cons harg hrest =>
          exact ⟨_, rfl, .eval harg henv
            (.cons (.callArgs found .nil hrest henv rfl) hkont)⟩
  | arrayEmpty item => exact ⟨_, rfl, .ret (ArrayValues.empty_typed _ item) hkont⟩
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

  | dataCtor foundData foundCtor fields =>
      cases fields with
      | nil => exact ⟨_, rfl, .ret (.data foundData foundCtor .nil) hkont⟩
      | cons field rest =>
          exact ⟨_, rfl, .eval field henv
            (.cons (.dataFields foundData foundCtor .nil rest henv rfl) hkont)⟩
  | dataCase foundData result scrutinee branches =>
      exact ⟨_, rfl, .eval scrutinee henv
        (.cons (.dataBranches foundData result branches henv) hkont)⟩

/-- A frame consumes a value of its input type without getting stuck. -/
theorem frame_step_typed (hprogram : ProgramTyped declarations program signatures)
    (hframe : FrameTyped declarations signatures frame α β)
    (hvalue : ValueTyped declarations value α) (hkont : KontTyped declarations signatures kont β τ) :
    ∃ next, Step program (.ret value (frame :: kont)) next ∧
      StateTyped declarations signatures next τ := by
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
  | inl other => exact ⟨_, rfl, .ret (.inl hvalue other) hkont⟩
  | inr other => exact ⟨_, rfl, .ret (.inr hvalue other) hkont⟩
  | sumBranches hleft hright henv =>
      rcases hvalue.sum_canonical with ⟨payload, rfl, hpayload⟩ |
        ⟨payload, rfl, hpayload⟩
      · exact ⟨_, rfl, .eval hleft (.cons hpayload henv) hkont⟩
      · exact ⟨_, rfl, .eval hright (.cons hpayload henv) hkont⟩
  | natBranches hzero hsucc henv =>
      obtain ⟨n, rfl, bounded⟩ := hvalue.nat_canonical
      cases n with
      | zero => exact ⟨_, rfl, .eval hzero henv hkont⟩
      | succ predecessor =>
          exact ⟨_, rfl, .eval hsucc
            (.cons (.nat (Nat.lt_trans (Nat.lt_succ_self _) bounded)) henv) hkont⟩
  | natBinLeft operation hright henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.natBinRight operation hvalue) hkont)⟩
  | natBinRight operation hleft =>
      obtain ⟨left, rfl, leftBound⟩ := hleft.nat_canonical
      obtain ⟨right, rfl, rightBound⟩ := hvalue.nat_canonical
      have outcome := evalNatBin_bounded (operation := operation) leftBound rightBound
      cases computed : evalNatBin operation left right with
      | value result =>
          simp only [computed] at outcome
          exact ⟨_, by simp [Step, step, computed], .ret (.nat outcome) hkont⟩
      | overflow fault =>
          simp only [computed] at outcome
          exact ⟨_, by simp [Step, step, computed],
            .overflow outcome.1 outcome.2.1 outcome.2.2 (hkont.wellFormed hprogram .nat64)⟩
  | natCmpLeft operation hright henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.natCmpRight operation hvalue) hkont)⟩
  | natCmpRight operation hleft =>
      obtain ⟨left, rfl, _⟩ := hleft.nat_canonical
      obtain ⟨right, rfl, _⟩ := hvalue.nat_canonical
      exact ⟨_, rfl, .ret .bool hkont⟩

  | structEqLeft hright domain henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.structEqRight hvalue domain) hkont)⟩
  | structEqRight hleft _ =>
      exact ⟨_, rfl, .ret .bool hkont⟩
  | wordBinLeft width operation hright henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.wordBinRight width operation hvalue) hkont)⟩
  | wordBinRight width operation hleft =>
      obtain ⟨left, rfl, leftBound⟩ := hleft.word_canonical
      obtain ⟨right, rfl, rightBound⟩ := hvalue.word_canonical
      exact ⟨_, by simp [Step, step],
        .ret (.word (evalWordBin_bounded (operation := operation) leftBound rightBound)) hkont⟩
  | wordCmpLeft width operation hright henv =>
      exact ⟨_, rfl, .eval hright henv (.cons (.wordCmpRight width operation hvalue) hkont)⟩
  | wordCmpRight width operation hleft =>
      obtain ⟨left, rfl, _⟩ := hleft.word_canonical
      obtain ⟨right, rfl, _⟩ := hvalue.word_canonical
      exact ⟨.ret (.bool (operation.apply left right)) _, by simp [Step, step], .ret .bool hkont⟩
  | wordOfNat target =>
      obtain ⟨value, rfl, _⟩ := hvalue.nat_canonical
      exact ⟨_, rfl, .ret (.word normalizeWord_bounded) hkont⟩
  | wordToNat source =>
      obtain ⟨value, rfl, bounded⟩ := hvalue.word_canonical
      exact ⟨_, by simp [Step, step], .ret (.nat (wordToNat_bounded bounded)) hkont⟩
  | wordCast source target =>
      obtain ⟨value, rfl, _⟩ := hvalue.word_canonical
      exact ⟨_, by simp [Step, step],
        .ret (.word (normalizeWord_bounded (width := target) (value := value))) hkont⟩

  | callArgs found hdone hremaining henv paramsEqual =>
      have hdone' := hdone.append (EnvTyped.cons hvalue .nil)
      cases hremaining with
      | nil =>
          have hargs : EnvTyped declarations _ _ := hdone'
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

  | dataFields foundData foundCtor hdone hremaining henv fieldsEqual =>
      have hdone' := hdone.append (EnvTyped.cons hvalue .nil)
      cases hremaining with
      | nil =>
          have hfields : EnvTyped declarations _ _ := hdone'
          rw [fieldsEqual] at hfields
          exact ⟨_, rfl, .ret (.data foundData foundCtor hfields) hkont⟩
      | cons hfield hrest =>
          exact ⟨_, rfl, .eval hfield henv
            (.cons (.dataFields foundData foundCtor hdone' hrest henv (by
              simpa only [List.append_assoc, List.singleton_append] using fieldsEqual)) hkont)⟩
  | dataBranches foundData _ hbranches henv =>
      obtain ⟨constructor, fields, constructors, fieldTypes, rfl,
        valueData, foundCtor, hfields⟩ := hvalue.data_canonical
      have same := Option.some.inj (foundData.symm.trans valueData)
      cases same
      obtain ⟨arity, body, foundBranch, arityEqual, hbody⟩ := hbranches.lookup foundCtor
      have actualArity : arity = fields.length := arityEqual.trans hfields.length.symm
      exact ⟨_, by simp [Step, step, foundBranch, actualArity],
        .eval hbody (hfields.append henv) hkont⟩

/-- Every typed state is terminal or takes a type-preserving step. -/
theorem safety_step (hprogram : ProgramTyped declarations program signatures)
    (typed : StateTyped declarations signatures state τ) :
    Terminal state ∨ ∃ next, Step program state next ∧ StateTyped declarations signatures next τ := by
  cases typed with
  | eval hexpr henv hkont => exact .inr (eval_step_typed hprogram hexpr henv hkont)
  | ret hvalue hkont =>
      cases hkont with
      | nil _ => exact .inl trivial
      | cons hframe hrest => exact .inr (frame_step_typed hprogram hframe hvalue hrest)
  | overflow hleft hright hoverflow _ => exact .inl ⟨hleft, hright, hoverflow⟩

theorem terminal_no_step (terminal : Terminal state) : step program state = none := by
  cases state with
  | eval expr env kont => exact False.elim terminal
  | ret value kont =>
      cases kont with
      | nil => rfl
      | cons frame rest => exact False.elim terminal
  | overflow operation left right => rfl

/-- One-step preservation for the independently defined machine. -/
theorem preservation (hprogram : ProgramTyped declarations program signatures)
    (typed : StateTyped declarations signatures state τ) (transition : Step program state next) :
    StateTyped declarations signatures next τ := by
  rcases safety_step hprogram typed with terminal | ⟨next', hstep, htyped⟩
  · have impossible : (none : Option State) = some next :=
      (terminal_no_step (program := program) terminal).symm.trans transition
    cases impossible
  · have same : next' = next := step_deterministic hstep transition
    cases same
    exact htyped

/-- Progress distinguishes permitted overflow from arbitrary stuckness. -/
theorem progress (hprogram : ProgramTyped declarations program signatures)
    (typed : StateTyped declarations signatures state τ) :
    Terminal state ∨ ∃ next, Step program state next := by
  rcases safety_step hprogram typed with terminal | ⟨next, hstep, _⟩
  · exact .inl terminal
  · exact .inr ⟨next, hstep⟩

theorem preservation_steps (hprogram : ProgramTyped declarations program signatures)
    (typed : StateTyped declarations signatures start τ) (execution : Steps program start final) :
    StateTyped declarations signatures final τ := by
  induction execution with
  | refl => exact typed
  | tail history transition ih => exact preservation hprogram ih transition

/-- A stuck state has no successor and is neither a return nor justified overflow. -/
def Stuck (program : Program) (state : State) : Prop := step program state = none ∧ ¬ Terminal state

theorem typed_not_stuck (hprogram : ProgramTyped declarations program signatures)
    (typed : StateTyped declarations signatures state τ) : ¬ Stuck program state := by
  intro stuck
  rcases progress hprogram typed with terminal | ⟨next, transition⟩
  · exact stuck.2 terminal
  · have impossible : (none : Option State) = some next := stuck.1.symm.trans transition
    cases impossible

/-- Type safety for every finite execution prefix from a typed configuration. -/
theorem type_safety (hprogram : ProgramTyped declarations program signatures)
    (typed : StateTyped declarations signatures start τ) (execution : Steps program start final) :
    StateTyped declarations signatures final τ ∧ ¬ Stuck program final := by
  have finalTyped := preservation_steps hprogram typed execution
  exact ⟨finalTyped, typed_not_stuck hprogram finalTyped⟩

/-- Closed source terms inherit the machine theorem through their initial state. -/
theorem closed_type_safety (hprogram : ProgramTyped declarations program signatures)
    (typed : ExprTyped declarations signatures [] expr τ)
    (execution : Steps program (initial expr) final) :
    StateTyped declarations signatures final τ ∧ ¬ Stuck program final :=
  type_safety hprogram (initial_typed hprogram typed) execution

/-- Successful executions return a value of the original result type. -/
theorem return_type (hprogram : ProgramTyped declarations program signatures)
    (typed : ExprTyped declarations signatures [] expr τ)
    (execution : Steps program (initial expr) (.ret value [])) : ValueTyped declarations value τ := by
  have finalTyped := preservation_steps hprogram (initial_typed hprogram typed) execution
  cases finalTyped with
  | ret hvalue hkont =>
      cases hkont
      exact hvalue

/-- A reached failure proves actual overflow of the recorded sum or product. -/
theorem overflow_is_justified (hprogram : ProgramTyped declarations program signatures)
    (typed : ExprTyped declarations signatures [] expr τ)
    (execution : Steps program (initial expr) (.overflow operation left right)) :
    Overflow operation left right := by
  have finalTyped := preservation_steps hprogram (initial_typed hprogram typed) execution
  cases finalTyped with
  | overflow hleft hright hoverflow _ => exact ⟨hleft, hright, hoverflow⟩

end LeanExe.TypeSafety
