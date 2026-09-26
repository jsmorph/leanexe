import Project.Drone.ExecutionInitialFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def unwindLoopBody : Wasm.Program :=
  match (func24[8]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def unwindParams (fuel index state : Nat) (terrain history row : UInt64) : List Value :=
  [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat state),
    .i64 terrain, .i64 terrain, .i64 history, .i64 history, .i64 row, .i64 row]

def unwindFrame (fuel index state : Nat) (terrain history row : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) : Locals :=
  { params := unwindParams fuel index state terrain history row,
    locals := [.i64 0, .i64 (if tracked then row else 0), .i64 0, .i64 out0, .i64 out1, .i64 0] ++
      (aux ++ s.words) }

macro "wp_unwind_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [unwindFrame, unwindParams, Scratch.words, List.length_append,
    List.length_cons, List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff,
    UInt64.lt_irrefl, $ts,*])

macro "unwind_controls" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_unwind_frame [$ts,*]) <;> (advance_wp_goal; first
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide, show (1 : UInt64) ≠ 0 by decide,
         Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
         UInt64.lt_irrefl, ↓reduceIte])))
   try wp_unwind_frame [$ts,*]))

theorem unwindFrame_as_push (fuel index state : Nat) (terrain history row : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) :
    unwindFrame fuel index state terrain history row tracked out0 out1 aux s =
      WordArrayPush.frame (unwindParams fuel index state terrain history row)
        ([.i64 0, .i64 (if tracked then row else 0), .i64 0, .i64 out0, .i64 out1, .i64 0] ++ aux) [] s := by
  simp [unwindFrame, WordArrayPush.frame]

theorem unwind_push_shapes : (unwindLoopBody.drop 18).take 67 = WordArrayPush.program 51 ∧
    (unwindLoopBody.drop 109).take 67 = WordArrayPush.program 51 := ⟨rfl, rfl⟩

end Project.Drone.Execution
