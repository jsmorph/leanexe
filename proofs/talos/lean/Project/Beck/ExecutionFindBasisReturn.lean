import Project.Beck.ExecutionFindBasisLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem findBasisEntry_exact (env : HostEnv Unit) (initial : Store Unit) (params : List Value)
    (paramsSize : params.length = 9) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := List.replicate 47 (.i64 0) })) :
    wp Project.Beck.«module» (func27.take 8) Q initial
      { params := params, locals := List.replicate 47 (.i64 0) } env := by
  simp only [func27, List.take]
  wp_run [paramsSize, List.replicate_succ, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  exact next

theorem findBasisEntry_state (basis : Basis) (rowOwner rowPointer columnOwner columnPointer : UInt64) :
    FindBasisLocals (List.replicate 47 (.i64 0)) false basis rowOwner rowPointer columnOwner columnPointer := by
  constructor <;> simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem findBasisReturn_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (stopped : Bool)
    (state : FindBasisLocals locals stopped basis rowOwner rowPointer columnOwner columnPointer) (Q : Assertion Unit)
    (next : ∀ frame, frame.values = basisValues basis rowOwner rowPointer columnOwner columnPointer → Q (.Fallthrough initial frame)) :
    wp Project.Beck.«module» (func27.drop 9) Q initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  cases stopped
  all_goals
    simp only [func27, List.drop]
    repeat' first
      | (wp_run [findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          state.size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil, state.flag, Bool.false_eq_true,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  · exact next _ rfl
  · obtain ⟨ro, rp, co, cp, determinant⟩ := state.result rfl
    wp_run [findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      state.size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil, ro, rp, co, cp, determinant]
    exact next _ rfl

#print axioms findBasisEntry_exact
#print axioms findBasisReturn_exact

end Project.Beck.Execution
