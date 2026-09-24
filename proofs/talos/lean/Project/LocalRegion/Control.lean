import Project.LocalRegion.Relation

namespace Project.LocalRegion
open Wasm

def finishBlock (results : Nat) (below : List Value) : Continuation α → Continuation α
  | .Fallthrough st frame | .Break 0 st frame =>
      .Fallthrough st { frame with values := frame.values.take results ++ below }
  | .Break (label + 1) st frame => .Break label st frame
  | result => result

theorem finishBlock_related (mapping : FrameMap rename domain Related)
    (hResult : ContinuationRel Related source target) (results : Nat) (below : List Value) :
    ContinuationRel Related (finishBlock results below source) (finishBlock results below target) := by
  cases hResult with
  | fallthrough h =>
      simp only [finishBlock, ← mapping.values h]
      exact .fallthrough (mapping.stack h _)
  | @«break» label st source target h =>
      cases label with
      | zero =>
          simp only [finishBlock, ← mapping.values h]
          exact .fallthrough (mapping.stack h _)
      | succ label => exact .break h
  | returned => exact .returned _ _
  | trap => exact .trap _ _
  | invalid => exact .invalid _
  | outOfFuel => exact .outOfFuel
  | returnCall => exact .returnCall _ _ _
  | throwing h => exact .throwing h

theorem block_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target)
    (hBody : ContinuationRel Related (exec fuel m st source body env)
      (exec fuel m st target (renameProgram rename body) env)) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source (.block params results body paramTypes resultTypes) env)
      (execOne (fuel + 1) m st target
        (.block params results (renameProgram rename body) paramTypes resultTypes) env) := by
  simp only [execOne.eq_def]
  change ContinuationRel Related
    (finishBlock results (source.values.drop params) (exec fuel m st source body env))
    (finishBlock results (target.values.drop params)
      (exec fuel m st target (renameProgram rename body) env))
  rw [← mapping.values hRelated]
  exact finishBlock_related mapping hBody results _

theorem branch_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target)
    (hThen : ∀ values, ContinuationRel Related
      (exec fuel m st { source with values := values } yes env)
      (exec fuel m st { target with values := values } (renameProgram rename yes) env))
    (hElse : ∀ values, ContinuationRel Related
      (exec fuel m st { source with values := values } no env)
      (exec fuel m st { target with values := values } (renameProgram rename no) env)) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source (.iff params results yes no paramTypes resultTypes) env)
      (execOne (fuel + 1) m st target
        (.iff params results (renameProgram rename yes) (renameProgram rename no)
          paramTypes resultTypes) env) := by
  simp only [execOne.eq_def, ← mapping.values hRelated]
  cases source.values with
  | nil => exact .invalid _
  | cons value values =>
      cases value <;> try exact .invalid _
      case i32 condition =>
        by_cases hCondition : condition ≠ 0
        · simp only [if_pos hCondition]
          exact finishBlock_related mapping (hThen values) results (values.drop params)
        · simp only [if_neg hCondition]
          exact finishBlock_related mapping (hElse values) results (values.drop params)

theorem loop_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target)
    (hBody : ContinuationRel Related (exec fuel m st source body env)
      (exec fuel m st target (renameProgram rename body) env))
    (hRestart : ∀ st source target, Related source target →
      ContinuationRel Related
        (execOne fuel m st source (.loop params results body paramTypes resultTypes) env)
        (execOne fuel m st target
          (.loop params results (renameProgram rename body) paramTypes resultTypes) env)) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source (.loop params results body paramTypes resultTypes) env)
      (execOne (fuel + 1) m st target
        (.loop params results (renameProgram rename body) paramTypes resultTypes) env) := by
  simp only [execOne_loop_succ]
  generalize hSource : exec fuel m st source body env = sourceResult at hBody ⊢
  generalize hTarget : exec fuel m st target (renameProgram rename body) env = targetResult at hBody ⊢
  cases hBody with
  | fallthrough h =>
      simp only [← mapping.values h, ← mapping.values hRelated]
      exact .fallthrough (mapping.stack h _)
  | @«break» label nextStore nextSource nextTarget h =>
      cases label with
      | zero =>
          simp only [← mapping.values h, ← mapping.values hRelated]
          exact hRestart _ _ _ (mapping.stack h _)
      | succ label => exact .break h
  | returned => exact .returned _ _
  | trap => exact .trap _ _
  | invalid => exact .invalid _
  | outOfFuel => exact .outOfFuel
  | returnCall => exact .returnCall _ _ _
  | throwing h => exact .throwing h

end Project.LocalRegion
