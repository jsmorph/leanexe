import LeanExe.TypeSafety.Safety

/-!
# Continuation extension and finite execution decomposition

Appending a continuation preserves each successful transition. At a completed
return with an empty stack, the added continuation can begin a new computation;
therefore an optional-step equation requires excluding that exact boundary.

These statements concern raw states and the same fixed program. They impose no
typing or termination premise, and retain malformed/stuck executions separately
from justified arithmetic overflow.
-/

namespace LeanExe.TypeSafety

/-- Append a pending continuation; arithmetic overflow already discards the stack. -/
def State.appendKont (state : State) (suffix : Kont) : State :=
  match state with
  | .eval expr env kont => .eval expr env (kont ++ suffix)
  | .ret value kont => .ret value (kont ++ suffix)
  | .overflow operation left right => .overflow operation left right

/-- A completed value whose next transition, if any, belongs to the added continuation. -/
def ReturnBoundary : State → Prop
  | .ret _ [] => True
  | _ => False

theorem returnBoundary_iff : ReturnBoundary state ↔ ∃ value, state = .ret value [] := by
  cases state with
  | eval expr env kont =>
      constructor
      · intro impossible; cases impossible
      · intro witness; obtain ⟨_, impossible⟩ := witness; cases impossible
  | ret value kont =>
      cases kont with
      | nil => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => True.intro⟩
      | cons frame rest =>
          constructor
          · intro impossible; cases impossible
          · intro witness; obtain ⟨_, impossible⟩ := witness; cases impossible
  | overflow operation left right =>
      constructor
      · intro impossible; cases impossible
      · intro witness; obtain ⟨_, impossible⟩ := witness; cases impossible

theorem returnBoundary_or_not (state : State) : ReturnBoundary state ∨ ¬ ReturnBoundary state := by
  cases state with
  | eval => exact .inr (fun impossible => impossible)
  | ret value kont =>
      cases kont with
      | nil => exact .inl True.intro
      | cons => exact .inr (fun impossible => impossible)
  | overflow => exact .inr (fun impossible => impossible)

theorem State.appendKont_nil (state : State) : state.appendKont [] = state := by
  cases state <;> simp only [State.appendKont, List.append_nil]

theorem State.appendKont_append (state : State) (firstPart lastPart : Kont) :
    (state.appendKont firstPart).appendKont lastPart = state.appendKont (firstPart ++ lastPart) := by
  cases state <;> simp only [State.appendKont, List.append_assoc]

theorem enterCall_appendKont :
    enterCall program function arguments (kont ++ suffix) =
      (enterCall program function arguments kont).map (fun state => state.appendKont suffix) := by
  cases found : lookup program function <;> simp only [enterCall, found, Option.map_none,
    Option.map_some, State.appendKont]

/-- Evaluation always begins inside the source computation, before any return boundary. -/
theorem eval_step_appendKont (expr : Expr) :
    step program (.eval expr env (kont ++ suffix)) =
      (step program (.eval expr env kont)).map (fun state => state.appendKont suffix) := by
  cases expr <;> try rfl
  case var index =>
    cases found : lookup env index <;> simp only [step, found] <;> rfl
  case call function arguments =>
    cases arguments with
    | nil => exact enterCall_appendKont
    | cons => rfl
  case dataCtor dataId constructor fields => cases fields <;> rfl

/-- An existing frame is processed before any appended continuation frame. -/
theorem ret_step_appendKont (frame : Frame) (value : Value) :
    step program (.ret value (frame :: (kont ++ suffix))) =
      (step program (.ret value (frame :: kont))).map (fun state => state.appendKont suffix) := by
  cases frame <;> try rfl
  case ifBranches yes no env => cases value <;> rfl
  case fst => cases value <;> rfl
  case snd => cases value <;> rfl
  case splitBody body env => cases value <;> rfl
  case unitBody body env => cases value <;> rfl
  case sumBranches left right env => cases value <;> rfl
  case natBranches zeroBody succBody env =>
    cases value <;> try rfl
    case nat number => cases number <;> rfl
  case natBinRight operation left =>
    cases value <;> cases left <;> try rfl
    rename_i right left
    cases result : evalNatBin operation left right <;> simp only [step, result] <;> rfl
  case natCmpRight operation left => cases value <;> cases left <;> rfl
  case wordBinRight width operation left =>
    cases value <;> cases left <;> try rfl
    rename_i rightWidth right leftWidth left
    by_cases matching : leftWidth = width ∧ rightWidth = width <;>
      simp only [step, matching] <;> rfl
  case wordCmpRight width operation left =>
    cases value <;> cases left <;> try rfl
    rename_i rightWidth right leftWidth left
    by_cases matching : leftWidth = width ∧ rightWidth = width <;>
      simp only [step, matching] <;> rfl
  case wordOfNat target => cases value <;> rfl
  case wordToNat source =>
    cases value <;> try rfl
    rename_i actual number
    by_cases matching : actual = source <;> simp only [step, matching] <;> rfl
  case wordCast source target =>
    cases value <;> try rfl
    rename_i actual number
    by_cases matching : actual = source <;> simp only [step, matching] <;> rfl
  case callArgs function done remaining env =>
    cases remaining with
    | nil => exact enterCall_appendKont
    | cons => rfl
  case arraySize => cases value <;> rfl
  case arrayGetArray index env => cases value <;> rfl
  case arrayGetIndex elements => cases value <;> rfl
  case arraySetArray index replacement env => cases value <;> rfl
  case arraySetIndex elements replacement env => cases value <;> rfl
  case arrayPushArray replacement env => cases value <;> rfl
  case arrayAppendLeft right env => cases value <;> rfl
  case arrayAppendRight left => cases value <;> rfl
  case dataFields dataId constructor done remaining env => cases remaining <;> rfl
  case dataBranches dataId branches env =>
    cases value <;> try rfl
    rename_i actualId constructor fields
    by_cases nominal : actualId = dataId
    · simp only [step, nominal]
      cases found : lookup branches constructor with
      | none => rfl
      | some branch =>
          obtain ⟨arity, body⟩ := branch
          by_cases arityMatches : arity = fields.length <;> simp only [arityMatches] <;> rfl
    · simp only [step, nominal]
      rfl

/-- The excluded case is precisely where the added continuation can begin execution. -/
theorem step_appendKont_of_not_boundary (notBoundary : ¬ ReturnBoundary state) :
    step program (state.appendKont suffix) =
      (step program state).map (fun next => next.appendKont suffix) := by
  cases state with
  | eval expr env kont => exact eval_step_appendKont expr
  | ret value kont =>
      cases kont with
      | nil => exact False.elim (notBoundary True.intro)
      | cons frame rest => exact ret_step_appendKont frame value
  | overflow operation left right => rfl

theorem Step.not_boundary (transition : Step program before after) : ¬ ReturnBoundary before := by
  intro boundary
  obtain ⟨value, same⟩ := returnBoundary_iff.mp boundary
  cases same
  cases transition

/-- A successful transition cannot cross from an already completed empty-stack return. -/
theorem Step.appendKont (transition : Step program before after) (suffix : Kont) :
    Step program (before.appendKont suffix) (after.appendKont suffix) := by
  change step program (before.appendKont suffix) = some (after.appendKont suffix)
  rw [step_appendKont_of_not_boundary transition.not_boundary]
  change (step program before).map _ = some (after.appendKont suffix)
  rw [show step program before = some after from transition]
  rfl

theorem Steps.appendKont (execution : Steps program before after) (suffix : Kont) :
    Steps program (before.appendKont suffix) (after.appendKont suffix) := by
  induction execution with
  | refl => exact .refl
  | tail history transition ih => exact .tail ih (transition.appendKont suffix)

/-- Before the boundary, every extended transition comes from a source transition. -/
theorem step_unappendKont (notBoundary : ¬ ReturnBoundary state)
    (transition : Step program (state.appendKont suffix) next) :
    ∃ sourceNext, Step program state sourceNext ∧ next = sourceNext.appendKont suffix := by
  change step program (state.appendKont suffix) = some next at transition
  rw [step_appendKont_of_not_boundary notBoundary] at transition
  cases found : step program state with
  | none => rw [found] at transition; cases transition
  | some sourceNext =>
      rw [found] at transition
      exact ⟨sourceNext, found, (Option.some.inj transition).symm⟩

theorem terminal_appendKont_iff_of_not_boundary (notBoundary : ¬ ReturnBoundary state) :
    Terminal (state.appendKont suffix) ↔ Terminal state := by
  cases state with
  | eval => exact Iff.rfl
  | ret value kont =>
      cases kont with
      | nil => exact False.elim (notBoundary True.intro)
      | cons => exact Iff.rfl
  | overflow => exact Iff.rfl

/-- A failed source computation stays stuck; boundary returns belong to the continuation instead. -/
theorem stuck_appendKont_iff_of_not_boundary (notBoundary : ¬ ReturnBoundary state) :
    Stuck program (state.appendKont suffix) ↔ Stuck program state := by
  constructor
  · intro stuck
    have noStep : step program state = none := by
      cases found : step program state with
      | none => rfl
      | some next =>
          have impossible := stuck.1
          rw [step_appendKont_of_not_boundary notBoundary, found] at impossible
          cases impossible
    exact ⟨noStep, fun terminal => stuck.2
      ((terminal_appendKont_iff_of_not_boundary notBoundary).mpr terminal)⟩
  · intro stuck
    refine ⟨?_, fun terminal => stuck.2
      ((terminal_appendKont_iff_of_not_boundary notBoundary).mp terminal)⟩
    rw [step_appendKont_of_not_boundary notBoundary, stuck.1]
    rfl

/-- Stuckness excludes the completed return boundary by definition. -/
theorem Stuck.not_boundary (stuck : Stuck program state) : ¬ ReturnBoundary state := by
  intro boundary
  obtain ⟨value, same⟩ := returnBoundary_iff.mp boundary
  cases same
  exact stuck.2 True.intro

theorem Stuck.appendKont (stuck : Stuck program state) (suffix : Kont) :
    Stuck program (state.appendKont suffix) :=
  (stuck_appendKont_iff_of_not_boundary stuck.not_boundary).mpr stuck

/-- Every finite extended execution either remains inside the source computation,
    or factors through its completed return and a continuation execution. -/
theorem steps_appendKont_decompose (execution : Steps program (state.appendKont suffix) final) :
    (∃ middle, Steps program state middle ∧ ¬ ReturnBoundary middle ∧
      final = middle.appendKont suffix) ∨
    (∃ value, Steps program state (.ret value []) ∧ Steps program (.ret value suffix) final) := by
  generalize startEq : state.appendKont suffix = start at execution
  induction execution with
  | refl =>
      rcases returnBoundary_or_not state with boundary | notBoundary
      · obtain ⟨value, same⟩ := returnBoundary_iff.mp boundary
        cases same
        refine .inr ⟨value, .refl, ?_⟩
        cases startEq
        exact .refl
      · exact .inl ⟨state, .refl, notBoundary, startEq.symm⟩
  | tail history transition ih =>
      rcases ih with unfinished | completed
      · obtain ⟨middle, sourceHistory, notBoundary, same⟩ := unfinished
        rw [same] at transition
        obtain ⟨sourceNext, sourceTransition, nextSame⟩ := step_unappendKont notBoundary transition
        have sourceExecution := Steps.tail sourceHistory sourceTransition
        rcases returnBoundary_or_not sourceNext with boundary | notBoundary
        · obtain ⟨value, sourceSame⟩ := returnBoundary_iff.mp boundary
          cases sourceSame
          refine .inr ⟨value, sourceExecution, ?_⟩
          cases nextSame
          exact .refl
        · exact .inl ⟨sourceNext, sourceExecution, notBoundary, nextSame⟩
      · obtain ⟨value, sourceExecution, continuationExecution⟩ := completed
        exact .inr ⟨value, sourceExecution, .tail continuationExecution transition⟩

/-- Exact normal-return sequencing, including reflection from the combined execution. -/
theorem appendKont_returns_iff :
    Steps program (state.appendKont suffix) (.ret result []) ↔
      ∃ value, Steps program state (.ret value []) ∧
        Steps program (.ret value suffix) (.ret result []) := by
  constructor
  · intro execution
    rcases steps_appendKont_decompose execution with unfinished | completed
    · obtain ⟨middle, sourceExecution, notBoundary, same⟩ := unfinished
      cases middle with
      | eval => cases same
      | ret value kont =>
          cases kont with
          | nil => exact False.elim (notBoundary True.intro)
          | cons => cases same
      | overflow => cases same
    · exact completed
  · intro witness
    obtain ⟨value, sourceExecution, continuationExecution⟩ := witness
    exact (sourceExecution.appendKont suffix).trans continuationExecution

/-- Overflow occurs either in the source or after it returns to the continuation.
    The exact record is preserved; its independent validity predicate is not weakened. -/
theorem appendKont_overflows_iff :
    Steps program (state.appendKont suffix) (.overflow operation left right) ↔
      Steps program state (.overflow operation left right) ∨
        ∃ value, Steps program state (.ret value []) ∧
          Steps program (.ret value suffix) (.overflow operation left right) := by
  constructor
  · intro execution
    rcases steps_appendKont_decompose execution with unfinished | completed
    · obtain ⟨middle, sourceExecution, notBoundary, same⟩ := unfinished
      cases middle with
      | eval => cases same
      | ret => cases same
      | overflow => cases same; exact .inl sourceExecution
    · exact .inr completed
  · intro witness
    rcases witness with sourceOverflow | continued
    · exact sourceOverflow.appendKont suffix
    · obtain ⟨value, sourceExecution, continuationExecution⟩ := continued
      exact (sourceExecution.appendKont suffix).trans continuationExecution

/-- Exact raw failure sequencing, without relabeling stuckness as permitted overflow. -/
theorem appendKont_reaches_stuck_iff :
    (∃ final, Steps program (state.appendKont suffix) final ∧ Stuck program final) ↔
      (∃ final, Steps program state final ∧ Stuck program final) ∨
        ∃ value final, Steps program state (.ret value []) ∧
          Steps program (.ret value suffix) final ∧ Stuck program final := by
  constructor
  · intro witness
    obtain ⟨final, execution, stuck⟩ := witness
    rcases steps_appendKont_decompose execution with unfinished | completed
    · obtain ⟨middle, sourceExecution, notBoundary, same⟩ := unfinished
      rw [same] at stuck
      exact .inl ⟨middle, sourceExecution,
        (stuck_appendKont_iff_of_not_boundary notBoundary).mp stuck⟩
    · obtain ⟨value, sourceExecution, continuationExecution⟩ := completed
      exact .inr ⟨value, final, sourceExecution, continuationExecution, stuck⟩
  · intro witness
    rcases witness with sourceStuck | continued
    · obtain ⟨final, execution, stuck⟩ := sourceStuck
      exact ⟨final.appendKont suffix, execution.appendKont suffix, stuck.appendKont suffix⟩
    · obtain ⟨value, final, sourceExecution, continuationExecution, stuck⟩ := continued
      exact ⟨final, (sourceExecution.appendKont suffix).trans continuationExecution, stuck⟩

end LeanExe.TypeSafety
