import Project.Drone.ExecutionInitialFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def historyLoopBody : Wasm.Program :=
  match (func22[8]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def historyParams (fuel index : Nat) (terrain previous history : UInt64) : List Value :=
  [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat index), .i64 terrain, .i64 terrain,
    .i64 previous, .i64 previous, .i64 history, .i64 history]

def historyFrame (fuel index : Nat) (terrain previous history out0 out1 : UInt64)
    (aux : List Value) (s : Scratch) : Locals :=
  { params := historyParams fuel index terrain previous history,
    locals := [.i64 0, .i64 0, .i64 0, .i64 out0, .i64 out1, .i64 0] ++ (aux ++ s.words) }

macro "wp_history_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [historyFrame, historyParams, Scratch.words, List.length_append,
    List.length_cons, List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff,
    UInt64.lt_irrefl, $ts,*])

macro "history_controls" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_history_frame [$ts,*]) <;> (advance_wp_goal; first
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide, show (1 : UInt64) ≠ 0 by decide,
         Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
         UInt64.lt_irrefl, ↓reduceIte])))
   try wp_history_frame [$ts,*]))

theorem historyFrame_as_push (fuel index : Nat) (terrain previous history out0 out1 : UInt64)
    (aux : List Value) (s : Scratch) :
    historyFrame fuel index terrain previous history out0 out1 aux s =
      WordArrayPush.frame (historyParams fuel index terrain previous history)
        ([.i64 0, .i64 0, .i64 0, .i64 out0, .i64 out1, .i64 0] ++ aux) [] s := by
  simp [historyFrame, WordArrayPush.frame]

end Project.Drone.Execution
