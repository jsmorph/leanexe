import Project.Drone.ExecutionAdvanceFrame
import Project.Drone.InitialSource

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def initialLoopBody : Wasm.Program :=
  match (func23[57]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

-- Tracking is a proof invariant; the emitted loop keeps the original seed root.
def initialFrame (seed row : UInt64) (state : Nat) (_tracked : Bool)
    (aux : List Value) (s : Scratch) (out0 out1 : UInt64) : Locals :=
  { params := [], locals :=
      [.i64 0, .i64 seed, .i64 seed, .i64 45, .i64 row, .i64 row] ++
      (aux ++ ([.i64 (UInt64.ofNat state), .i64 45, .i64 1] ++
        (s.words ++ [.i64 0, .i64 out0, .i64 out1, .i64 seed, .i64 0]))) }

macro "wp_initial_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [initialFrame, Scratch.words, List.length_append, List.length_cons,
    List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff,
    UInt64.lt_irrefl, UInt32.and_self, UInt32.and_zero, UInt32.zero_and, $ts,*])

macro "initial_calls" call:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_initial_frame [$ts,*]) <;> (advance_wp_goal; first
    | (refine wp_call_tw $call ?_;
       rintro finish values ⟨hFinish, hValues⟩; subst finish; rw [hValues])
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide,
         show (1 : UInt64) ≠ 0 by decide,
         Bool.false_eq_true, Bool.true_eq_false,
         not_false_eq_true, not_true_eq_false, UInt64.lt_irrefl,
         UInt32.and_self, UInt32.and_zero, UInt32.zero_and, ↓reduceIte])))
   try wp_initial_frame [$ts,*]))

theorem initialFrame_as_push (seed row : UInt64) (state : Nat) (tracked : Bool)
    (aux : List Value) (s : Scratch) (out0 out1 : UInt64) :
    initialFrame seed row state tracked aux s out0 out1 = WordArrayPush.frame []
      ([.i64 0, .i64 seed, .i64 seed, .i64 45, .i64 row, .i64 row] ++
        (aux ++ [.i64 (UInt64.ofNat state), .i64 45, .i64 1]))
      [.i64 0, .i64 out0, .i64 out1, .i64 seed, .i64 0] s := by
  simp only [initialFrame, WordArrayPush.frame, List.append_assoc]

theorem initial_push_shape : (initialLoopBody.drop 25).take 67 = WordArrayPush.program 28 := rfl

end Project.Drone.Execution
