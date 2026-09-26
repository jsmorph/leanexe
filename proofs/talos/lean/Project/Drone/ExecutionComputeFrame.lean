import Project.Drone.ExecutionUnwindFrame
import Project.Drone.ExecutionEmptyProgram

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def computeReject : Wasm.Program :=
  match (func25[19]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []
def computeValidate : Wasm.Program :=
  match (func25[19]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []
def computeAccept : Wasm.Program :=
  match (computeValidate[22]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []
def computeBadHeight : Wasm.Program :=
  match (computeValidate[22]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def computeFrame (terrain : UInt64) (aux : List Value) (s : Scratch) : Locals :=
  frame [.i64 terrain] aux [] s

macro "wp_compute_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [computeFrame, frame, Scratch.words, List.length_append,
    List.length_cons, List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff, $ts,*])

macro "compute_controls" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_compute_frame [$ts,*]) <;> (advance_wp_goal; first
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide, show (1 : UInt64) ≠ 0 by decide,
         Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
         UInt64.lt_irrefl, ↓reduceIte])))
   try wp_compute_frame [$ts,*]))

set_option maxRecDepth 32768 in
theorem compute_empty_shapes : (computeAccept.drop 26).take 40 = emptyProgram 31 ∧
    (computeAccept.drop 115).take 40 = emptyProgram 31 ∧
    computeReject.take 40 = emptyProgram 31 ∧ computeBadHeight.take 40 = emptyProgram 31 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Project.Drone.Execution
