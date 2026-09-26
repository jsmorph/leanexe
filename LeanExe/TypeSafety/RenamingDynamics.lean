import LeanExe.TypeSafety.RenamingEnvironments
import LeanExe.TypeSafety.Safety

/-!
# Raw operational correspondence under renaming

Each suspended expression is related using its own captured environment and
index mapping. Values, function identities, nominal identities, constructor
arities, and primitive operands remain identical. Calls enter unchanged program
bodies with the same fresh argument values.

The relation has no typing premise. Exact agreement on absent lookups is needed
as well as successful lookups, so malformed configurations remain observable.
Both directions preserve finite returned values, exact overflow records, and
reachability of stuck states in the same fixed program. This proves neither
termination nor any correspondence with extraction or compiled code.
-/

namespace LeanExe.TypeSafety

/-- Every captured expression has a mapping for its own lexical environment. -/
inductive FrameCorresponds : Frame → Frame → Prop where
  | letBody : EnvCorresponds mapping env env' →
      FrameCorresponds (.letBody body env) (.letBody (body.rename (Renaming.lift mapping)) env')
  | ifBranches : EnvCorresponds mapping env env' →
      FrameCorresponds (.ifBranches yes no env)
        (.ifBranches (yes.rename mapping) (no.rename mapping) env')
  | pairLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.pairLeft right env) (.pairLeft (right.rename mapping) env')
  | pairRight : FrameCorresponds (.pairRight left) (.pairRight left)
  | fst : FrameCorresponds .fst .fst
  | snd : FrameCorresponds .snd .snd
  | splitBody : EnvCorresponds mapping env env' →
      FrameCorresponds (.splitBody body env)
        (.splitBody (body.rename (Renaming.liftN 2 mapping)) env')
  | unitBody : EnvCorresponds mapping env env' →
      FrameCorresponds (.unitBody body env) (.unitBody (body.rename mapping) env')
  | inl : FrameCorresponds .inl .inl
  | inr : FrameCorresponds .inr .inr
  | sumBranches : EnvCorresponds mapping env env' →
      FrameCorresponds (.sumBranches left right env)
        (.sumBranches (left.rename (Renaming.lift mapping))
          (right.rename (Renaming.lift mapping)) env')
  | natBranches : EnvCorresponds mapping env env' →
      FrameCorresponds (.natBranches zeroBody succBody env)
        (.natBranches (zeroBody.rename mapping) (succBody.rename (Renaming.lift mapping)) env')
  | natBinLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.natBinLeft operation right env)
        (.natBinLeft operation (right.rename mapping) env')
  | natCmpLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.natCmpLeft operation right env)
        (.natCmpLeft operation (right.rename mapping) env')
  | natBinRight : FrameCorresponds (.natBinRight operation left) (.natBinRight operation left)
  | natCmpRight : FrameCorresponds (.natCmpRight operation left) (.natCmpRight operation left)
  | structEqLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.structEqLeft right env) (.structEqLeft (right.rename mapping) env')
  | structEqRight : FrameCorresponds (.structEqRight left) (.structEqRight left)
  | wordBinLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.wordBinLeft width operation right env)
        (.wordBinLeft width operation (right.rename mapping) env')
  | wordBinRight :
      FrameCorresponds (.wordBinRight width operation left) (.wordBinRight width operation left)
  | wordCmpLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.wordCmpLeft width operation right env)
        (.wordCmpLeft width operation (right.rename mapping) env')
  | wordCmpRight :
      FrameCorresponds (.wordCmpRight width operation left) (.wordCmpRight width operation left)
  | wordOfNat : FrameCorresponds (.wordOfNat target) (.wordOfNat target)
  | wordToNat : FrameCorresponds (.wordToNat source) (.wordToNat source)
  | wordCast : FrameCorresponds (.wordCast source target) (.wordCast source target)
  | callArgs : EnvCorresponds mapping env env' →
      FrameCorresponds (.callArgs function done remaining env)
        (.callArgs function done (renameArgs mapping remaining) env')
  | arraySize : FrameCorresponds .arraySize .arraySize
  | arrayGetArray : EnvCorresponds mapping env env' →
      FrameCorresponds (.arrayGetArray index env) (.arrayGetArray (index.rename mapping) env')
  | arrayGetIndex : FrameCorresponds (.arrayGetIndex elements) (.arrayGetIndex elements)
  | arraySetArray : EnvCorresponds mapping env env' →
      FrameCorresponds (.arraySetArray index replacement env)
        (.arraySetArray (index.rename mapping) (replacement.rename mapping) env')
  | arraySetIndex : EnvCorresponds mapping env env' →
      FrameCorresponds (.arraySetIndex elements replacement env)
        (.arraySetIndex elements (replacement.rename mapping) env')
  | arraySetValue : FrameCorresponds (.arraySetValue elements index) (.arraySetValue elements index)
  | arrayPushArray : EnvCorresponds mapping env env' →
      FrameCorresponds (.arrayPushArray value env) (.arrayPushArray (value.rename mapping) env')
  | arrayPushValue : FrameCorresponds (.arrayPushValue elements) (.arrayPushValue elements)
  | arrayAppendLeft : EnvCorresponds mapping env env' →
      FrameCorresponds (.arrayAppendLeft right env) (.arrayAppendLeft (right.rename mapping) env')
  | arrayAppendRight : FrameCorresponds (.arrayAppendRight left) (.arrayAppendRight left)
  | dataFields : EnvCorresponds mapping env env' →
      FrameCorresponds (.dataFields dataId constructor done remaining env)
        (.dataFields dataId constructor done (renameArgs mapping remaining) env')
  | dataBranches : EnvCorresponds mapping env env' →
      FrameCorresponds (.dataBranches dataId branches env)
        (.dataBranches dataId (renameBranches mapping branches) env')

inductive KontCorresponds : Kont → Kont → Prop where
  | nil : KontCorresponds [] []
  | cons : FrameCorresponds frame frame' → KontCorresponds rest rest' →
      KontCorresponds (frame :: rest) (frame' :: rest')

inductive StateCorresponds : State → State → Prop where
  | eval : EnvCorresponds mapping env env' → KontCorresponds kont kont' →
      StateCorresponds (.eval expr env kont) (.eval (expr.rename mapping) env' kont')
  | ret : KontCorresponds kont kont' → StateCorresponds (.ret value kont) (.ret value kont')
  | overflow : StateCorresponds (.overflow operation left right) (.overflow operation left right)

/-- Both computations lack a successor, or their successors correspond. -/
inductive OptionStatesCorrespond : Option State → Option State → Prop where
  | none : OptionStatesCorrespond none none
  | some : StateCorresponds state state' → OptionStatesCorrespond (some state) (some state')

/-- Fresh callees use the same code and argument environment on both sides. -/
theorem StateCorresponds.eval_same (konts : KontCorresponds kont kont') (expr : Expr) (env : Env) :
    StateCorresponds (.eval expr env kont) (.eval expr env kont') := by
  simpa only [Expr.rename_id] using
    (StateCorresponds.eval (expr := expr) (EnvCorresponds.refl env) konts)

theorem OptionStatesCorrespond.none_iff (corresponds : OptionStatesCorrespond first second) :
    first = Option.none ↔ second = Option.none := by
  cases corresponds with
  | none => exact Iff.rfl
  | some states => constructor <;> intro impossible <;> cases impossible

/-- The shared program table either lacks the callee on both sides or enters identical code. -/
theorem enterCall_corresponds (konts : KontCorresponds kont kont') :
    OptionStatesCorrespond (enterCall program function arguments kont)
      (enterCall program function arguments kont') := by
  cases found : lookup program function with
  | none => simp only [enterCall, found, Option.map_none]; exact .none
  | some body =>
      simp only [enterCall, found, Option.map_some]
      exact .some (StateCorresponds.eval_same konts body arguments)

/-- Evaluation of each raw expression preserves exact step-result correspondence. -/
theorem eval_step_corresponds (envs : EnvCorresponds mapping env env')
    (konts : KontCorresponds kont kont') (expr : Expr) :
    OptionStatesCorrespond (step program (.eval expr env kont))
      (step program (.eval (expr.rename mapping) env' kont')) := by
  cases expr with
  | var index =>
      cases found : lookup env index with
      | none =>
          simp only [Expr.rename, step, envs.lookup index, found, Option.map_none]
          exact .none
      | some value =>
          simp only [Expr.rename, step, envs.lookup index, found, Option.map_some]
          exact .some (.ret konts)
  | unit | bool _ | nat _ | word _ _ | arrayEmpty _ => exact .some (.ret konts)
  | letE bound body => exact .some (.eval envs (.cons (.letBody envs) konts))
  | ifE condition yes no => exact .some (.eval envs (.cons (.ifBranches envs) konts))
  | pair left right => exact .some (.eval envs (.cons (.pairLeft envs) konts))
  | fst pair => exact .some (.eval envs (.cons .fst konts))
  | snd pair => exact .some (.eval envs (.cons .snd konts))
  | split pair body => exact .some (.eval envs (.cons (.splitBody envs) konts))
  | unitCase scrutinee body => exact .some (.eval envs (.cons (.unitBody envs) konts))
  | inl _ payload => exact .some (.eval envs (.cons .inl konts))
  | inr _ payload => exact .some (.eval envs (.cons .inr konts))
  | sumCase scrutinee left right => exact .some (.eval envs (.cons (.sumBranches envs) konts))
  | natCase scrutinee zeroBody succBody => exact .some (.eval envs (.cons (.natBranches envs) konts))
  | natBin operation left right => exact .some (.eval envs (.cons (.natBinLeft envs) konts))
  | natCmp operation left right => exact .some (.eval envs (.cons (.natCmpLeft envs) konts))
  | structEq left right => exact .some (.eval envs (.cons (.structEqLeft envs) konts))
  | wordBin width operation left right => exact .some (.eval envs (.cons (.wordBinLeft envs) konts))
  | wordCmp width operation left right => exact .some (.eval envs (.cons (.wordCmpLeft envs) konts))
  | wordOfNat target value => exact .some (.eval envs (.cons .wordOfNat konts))
  | wordToNat source value => exact .some (.eval envs (.cons .wordToNat konts))
  | wordCast source target value => exact .some (.eval envs (.cons .wordCast konts))
  | call function arguments =>
      cases arguments with
      | nil => exact enterCall_corresponds konts
      | cons argument rest => exact .some (.eval envs (.cons (.callArgs envs) konts))
  | arraySize array => exact .some (.eval envs (.cons .arraySize konts))
  | arrayGet? array index => exact .some (.eval envs (.cons (.arrayGetArray envs) konts))
  | arraySet? array index replacement => exact .some (.eval envs (.cons (.arraySetArray envs) konts))
  | arrayPush? array value => exact .some (.eval envs (.cons (.arrayPushArray envs) konts))
  | arrayAppend? left right => exact .some (.eval envs (.cons (.arrayAppendLeft envs) konts))
  | dataCtor dataId constructor fields =>
      cases fields with
      | nil => exact .some (.ret konts)
      | cons field rest => exact .some (.eval envs (.cons (.dataFields envs) konts))
  | dataCase dataId result scrutinee branches =>
      exact .some (.eval envs (.cons (.dataBranches envs) konts))

/-- Frame correspondence includes every successful and malformed return transition. -/
theorem ret_step_corresponds (frames : FrameCorresponds frame frame')
    (konts : KontCorresponds kont kont') (value : Value) :
    OptionStatesCorrespond (step program (.ret value (frame :: kont)))
      (step program (.ret value (frame' :: kont'))) := by
  cases frames with
  | letBody envs => exact .some (.eval (envs.lift value) konts)
  | ifBranches envs =>
      cases value <;> try exact .none
      rename_i condition
      cases condition <;> exact .some (.eval envs konts)
  | pairLeft envs => exact .some (.eval envs (.cons .pairRight konts))
  | pairRight => exact .some (.ret konts)
  | fst | snd => cases value <;> first | exact .none | exact .some (.ret konts)
  | splitBody envs =>
      cases value <;> try exact .none
      rename_i left right
      exact .some (.eval (EnvCorresponds.lift (envs.lift right) left) konts)
  | unitBody envs => cases value <;> first | exact .none | exact .some (.eval envs konts)
  | inl | inr => exact .some (.ret konts)
  | sumBranches envs =>
      cases value <;> first | exact .none | exact .some (.eval (envs.lift _) konts)
  | natBranches envs =>
      cases value <;> try exact .none
      rename_i number
      cases number with
      | zero => exact .some (.eval envs konts)
      | succ predecessor => exact .some (.eval (envs.lift (.nat predecessor)) konts)
  | natBinLeft envs => exact .some (.eval envs (.cons .natBinRight konts))
  | natCmpLeft envs => exact .some (.eval envs (.cons .natCmpRight konts))
  | structEqLeft envs => exact .some (.eval envs (.cons .structEqRight konts))
  | structEqRight => exact .some (.ret konts)
  | wordBinLeft envs => exact .some (.eval envs (.cons .wordBinRight konts))
  | wordCmpLeft envs => exact .some (.eval envs (.cons .wordCmpRight konts))
  | @natBinRight operation left =>
      cases value <;> cases left <;> try exact .none
      rename_i right left
      cases result : evalNatBin operation left right with
      | value resultValue =>
          simp only [step, result]
          exact .some (.ret konts)
      | overflow fault =>
          simp only [step, result]
          exact .some .overflow
  | @natCmpRight operation left =>
      cases value <;> cases left <;> first | exact .none | exact .some (.ret konts)
  | @wordBinRight width operation left =>
      cases value <;> cases left <;> try exact .none
      rename_i rightWidth right leftWidth left
      by_cases matching : leftWidth = width ∧ rightWidth = width
      · simp only [step, matching]
        exact .some (.ret konts)
      · simp only [step, matching]
        exact .none
  | @wordCmpRight width operation left =>
      cases value <;> cases left <;> try exact .none
      rename_i rightWidth right leftWidth left
      by_cases matching : leftWidth = width ∧ rightWidth = width
      · simp only [step, matching]
        exact .some (.ret konts)
      · simp only [step, matching]
        exact .none
  | wordOfNat => cases value <;> first | exact .none | exact .some (.ret konts)
  | @wordToNat source =>
      cases value <;> try exact .none
      rename_i actual number
      by_cases matching : actual = source
      · simp only [step, matching]
        exact .some (.ret konts)
      · simp only [step, matching]
        exact .none
  | @wordCast source target =>
      cases value <;> try exact .none
      rename_i actual number
      by_cases matching : actual = source
      · simp only [step, matching]
        exact .some (.ret konts)
      · simp only [step, matching]
        exact .none
  | @callArgs mapping env env' function done remaining envs =>
      cases remaining with
      | nil => exact enterCall_corresponds konts
      | cons argument rest => exact .some (.eval envs (.cons (.callArgs envs) konts))
  | arraySize => cases value <;> first | exact .none | exact .some (.ret konts)
  | arrayGetArray envs =>
      cases value <;> first | exact .none | exact .some (.eval envs (.cons .arrayGetIndex konts))
  | arrayGetIndex => cases value <;> first | exact .none | exact .some (.ret konts)
  | arraySetArray envs =>
      cases value <;> first | exact .none | exact .some (.eval envs (.cons (.arraySetIndex envs) konts))
  | arraySetIndex envs =>
      cases value <;> first | exact .none | exact .some (.eval envs (.cons .arraySetValue konts))
  | arraySetValue => exact .some (.ret konts)
  | arrayPushArray envs =>
      cases value <;> first | exact .none | exact .some (.eval envs (.cons .arrayPushValue konts))
  | arrayPushValue => exact .some (.ret konts)
  | arrayAppendLeft envs =>
      cases value <;> first | exact .none | exact .some (.eval envs (.cons .arrayAppendRight konts))
  | arrayAppendRight => cases value <;> first | exact .none | exact .some (.ret konts)
  | @dataFields mapping env env' dataId constructor done remaining envs =>
      cases remaining with
      | nil => exact .some (.ret konts)
      | cons field rest => exact .some (.eval envs (.cons (.dataFields envs) konts))
  | @dataBranches mapping env env' dataId branches envs =>
      cases value <;> try exact .none
      rename_i actualId constructor fields
      by_cases nominal : actualId = dataId
      · simp only [step, nominal, renameBranches_lookup]
        cases found : lookup branches constructor with
        | none =>
            simp only [Option.map_none]
            exact .none
        | some branch =>
            obtain ⟨arity, body⟩ := branch
            simp only [Option.map_some]
            by_cases arityMatches : arity = fields.length
            · simp only [arityMatches]
              exact .some (.eval (envs.prefix fields) konts)
            · simp only [arityMatches]
              exact .none
      · simp only [step, nominal]
        exact .none

/-- The raw machine takes corresponding steps, or has no successor on either side. -/
theorem StateCorresponds.step (states : StateCorresponds first second) :
    OptionStatesCorrespond (LeanExe.TypeSafety.step program first)
      (LeanExe.TypeSafety.step program second) := by
  cases states with
  | eval envs konts => exact eval_step_corresponds envs konts _
  | ret konts =>
      cases konts with
      | nil => exact .none
      | cons frames rest => exact ret_step_corresponds frames rest _
  | overflow => exact .none

theorem StateCorresponds.step_none_iff (states : StateCorresponds first second) :
    LeanExe.TypeSafety.step program first = none ↔
      LeanExe.TypeSafety.step program second = none :=
  (states.step (program := program)).none_iff

/-- Legitimate overflow remains governed by the same mathematical predicate. -/
theorem StateCorresponds.terminal_iff (states : StateCorresponds first second) :
    Terminal first ↔ Terminal second := by
  cases states with
  | eval envs konts => exact Iff.rfl
  | ret konts => cases konts <;> exact Iff.rfl
  | overflow => exact Iff.rfl

theorem StateCorresponds.stuck_iff (states : StateCorresponds first second) :
    Stuck program first ↔ Stuck program second := by
  constructor
  · intro stuck
    exact ⟨states.step_none_iff.mp stuck.1,
      fun terminal => stuck.2 (states.terminal_iff.mpr terminal)⟩
  · intro stuck
    exact ⟨states.step_none_iff.mpr stuck.1,
      fun terminal => stuck.2 (states.terminal_iff.mp terminal)⟩

theorem OptionStatesCorrespond.some_left
    (outputs : OptionStatesCorrespond (Option.some state) result) :
    ∃ state', result = Option.some state' ∧ StateCorresponds state state' := by
  cases outputs with
  | some following => exact ⟨_, rfl, following⟩

theorem OptionStatesCorrespond.some_right
    (outputs : OptionStatesCorrespond result (Option.some state')) :
    ∃ state, result = Option.some state ∧ StateCorresponds state state' := by
  cases outputs with
  | some following => exact ⟨_, rfl, following⟩

theorem StateCorresponds.step_forward (states : StateCorresponds first second)
    (transition : Step program first next) :
    ∃ next', Step program second next' ∧ StateCorresponds next next' := by
  have outputs := states.step (program := program)
  change LeanExe.TypeSafety.step program first = some next at transition
  rw [transition] at outputs
  exact outputs.some_left

theorem StateCorresponds.step_backward (states : StateCorresponds first second)
    (transition : Step program second next') :
    ∃ next, Step program first next ∧ StateCorresponds next next' := by
  have outputs := states.step (program := program)
  change LeanExe.TypeSafety.step program second = some next' at transition
  rw [transition] at outputs
  exact outputs.some_right

/-- Each finite source execution has a corresponding target execution. -/
theorem StateCorresponds.steps_forward (states : StateCorresponds first second)
    (execution : Steps program first final) :
    ∃ final', Steps program second final' ∧ StateCorresponds final final' := by
  induction execution with
  | refl => exact ⟨_, .refl, states⟩
  | tail history transition ih =>
      obtain ⟨middle', history', middleStates⟩ := ih
      obtain ⟨final', transition', finalStates⟩ := middleStates.step_forward transition
      exact ⟨final', .tail history' transition', finalStates⟩

/-- The reverse execution argument uses the same relation, not an inverse variable map. -/
theorem StateCorresponds.steps_backward (states : StateCorresponds first second)
    (execution : Steps program second final') :
    ∃ final, Steps program first final ∧ StateCorresponds final final' := by
  induction execution with
  | refl => exact ⟨_, .refl, states⟩
  | tail history transition ih =>
      obtain ⟨middle, history', middleStates⟩ := ih
      obtain ⟨final, transition', finalStates⟩ := middleStates.step_backward transition
      exact ⟨final, .tail history' transition', finalStates⟩

/-- Renaming preserves and reflects every exact returned value, without typing premises. -/
theorem rename_returns_iff (envs : EnvCorresponds mapping env env') :
    Steps program (.eval expr env []) (.ret value []) ↔
      Steps program (.eval (expr.rename mapping) env' []) (.ret value []) := by
  constructor
  · intro execution
    obtain ⟨final', renamedExecution, states⟩ :=
      (StateCorresponds.eval envs .nil).steps_forward execution
    cases states with
    | ret konts => cases konts; exact renamedExecution
  · intro execution
    obtain ⟨final, originalExecution, states⟩ :=
      (StateCorresponds.eval envs .nil).steps_backward execution
    cases states with
    | ret konts => cases konts; exact originalExecution

/-- The operation tag and both mathematical operands of overflow are unchanged. -/
theorem rename_overflows_iff (envs : EnvCorresponds mapping env env') :
    Steps program (.eval expr env []) (.overflow operation left right) ↔
      Steps program (.eval (expr.rename mapping) env' []) (.overflow operation left right) := by
  constructor
  · intro execution
    obtain ⟨final', renamedExecution, states⟩ :=
      (StateCorresponds.eval envs .nil).steps_forward execution
    cases states
    exact renamedExecution
  · intro execution
    obtain ⟨final, originalExecution, states⟩ :=
      (StateCorresponds.eval envs .nil).steps_backward execution
    cases states
    exact originalExecution

/-- Malformed finite executions are reflected as well as preserved. -/
theorem rename_reaches_stuck_iff (envs : EnvCorresponds mapping env env') :
    (∃ final, Steps program (.eval expr env []) final ∧ Stuck program final) ↔
      ∃ final', Steps program (.eval (expr.rename mapping) env' []) final' ∧ Stuck program final' := by
  constructor
  · intro witness
    obtain ⟨final, execution, stuck⟩ := witness
    obtain ⟨final', renamedExecution, states⟩ :=
      (StateCorresponds.eval envs .nil).steps_forward execution
    exact ⟨final', renamedExecution, states.stuck_iff.mp stuck⟩
  · intro witness
    obtain ⟨final', execution, stuck⟩ := witness
    obtain ⟨final, originalExecution, states⟩ :=
      (StateCorresponds.eval envs .nil).steps_backward execution
    exact ⟨final, originalExecution, states.stuck_iff.mpr stuck⟩

end LeanExe.TypeSafety
