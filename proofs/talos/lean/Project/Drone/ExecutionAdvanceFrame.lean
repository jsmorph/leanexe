import Project.Drone.ExecutionBest
import Project.Drone.ExecutionPushBudget
import Project.ProofKit.ConstIf

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

def advanceLoopBody : Wasm.Program :=
  match (func18[6]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def advanceFrame (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer : UInt64)
    (aux : List Value) (s : Scratch) : Locals :=
  { params := [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat target), .i64 r0, .i64 r1,
      .i64 (if last then 1 else 0), .i64 previousOwner, .i64 previousPointer, .i64 rowOwner, .i64 rowPointer],
    locals := [.i64 tracker, .i64 0, .i64 resultOwner, .i64 resultPointer, .i64 0] ++
      (aux ++ s.words) }

def advanceChoice (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64) (target : Nat) : Choice :=
  if !last || target == 0 then bestPredecessor stateCount r0 r1 previous target else unreachable

macro "wp_advance_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [advanceFrame, Scratch.words, List.length_append, List.length_cons,
    List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff,
    UInt64.lt_irrefl, $ts,*])

elab "advance_wp_goal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainTarget
  unless goal.isAppOf ``Wasm.wp do
    throwError "advance instruction execution reached its postcondition"

macro "advance_calls" firstCall:ident secondCall:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_advance_frame [$ts,*]) <;> (advance_wp_goal; first
    | (refine wp_call_tw $firstCall ?_;
       rintro finish values ⟨hFinish, hValues⟩; subst finish; rw [hValues])
    | (refine wp_call_tw $secondCall ?_;
       rintro finish values ⟨hFinish, hValues⟩; subst finish; rw [hValues])
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide,
         show (1 : UInt64) ≠ 0 by decide,
         Bool.false_eq_true, Bool.true_eq_false,
         not_false_eq_true, not_true_eq_false, UInt64.lt_irrefl, ↓reduceIte])))
   try wp_advance_frame [$ts,*]))

theorem advanceFrame_as_push (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer : UInt64)
    (aux : List Value) (s : Scratch) :
    advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
      resultOwner resultPointer aux s = WordArrayPush.frame
      [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat target), .i64 r0, .i64 r1,
        .i64 (if last then 1 else 0), .i64 previousOwner, .i64 previousPointer, .i64 rowOwner, .i64 rowPointer]
      ([.i64 tracker, .i64 0, .i64 resultOwner, .i64 resultPointer, .i64 0] ++ aux) [] s := by
  simp only [advanceFrame, WordArrayPush.frame, List.append_assoc, List.append_nil]

end Project.Drone.Execution
