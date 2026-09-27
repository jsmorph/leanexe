import Project.Beck.ExecutionComputeState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem ComputeInputLocals.preserved {before after : List Value} {input : Input} {owner root : UInt64}
    (state : ComputeInputLocals before input owner root) (update : WordUpdate before after 14 65) :
    ComputeInputLocals after input owner root := by
  refine ⟨update.size.trans state.size, update.words, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (update.keeps 8 (Or.inl (by decide))).trans state.status
  · exact (update.keeps 9 (Or.inl (by decide))).trans state.jobs
  · exact (update.keeps 10 (Or.inl (by decide))).trans state.categories
  · exact (update.keeps 11 (Or.inl (by decide))).trans state.overlap
  · exact (update.keeps 12 (Or.inl (by decide))).trans state.owner
  · exact (update.keeps 13 (Or.inl (by decide))).trans state.pointer

def computePreparedLocals (locals : List Value) (input : Input) (owner root : UInt64) : List Value :=
  ((((((((((locals.set 15 (.i64 input.jobs.toUInt64)).set 16 (.i64 input.status)).set 17 (.i64 input.jobs.toUInt64)).set 18 (.i64 input.categories.toUInt64)).set 19 (.i64 input.overlap.toUInt64)).set 20 (.i64 owner)).set 21 (.i64 root)).set 24 (.i64 1)).set 22 (.i64 input.jobs.toUInt64)).set 56 (.i64 input.jobs.toUInt64)).set 59 (.i64 0)

set_option maxRecDepth 4096 in
theorem computePrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer : UInt64) (input : Input) (owner root : UInt64) (state : ComputeInputLocals locals input owner root)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := computePreparedLocals locals input owner root })) :
    wp Project.Beck.«module» (computeAccepted.take 22) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  simp only [computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [state.size, state.status, state.jobs, state.categories, state.overlap, state.owner, state.pointer,
    List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

theorem computePrepared_update {locals : List Value} (typed : WordLocals locals) (input : Input) (owner root : UInt64) :
    WordUpdate locals (computePreparedLocals locals input owner root) 14 65 := by
  unfold computePreparedLocals
  repeat' apply WordUpdate.set
  all_goals first | exact WordUpdate.refl typed 14 65 | decide

set_option maxRecDepth 4096 in
theorem computeStatus_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer : UInt64) (input : Input) (owner root : UInt64) (state : ComputeInputLocals locals input owner root)
    (accepted : input.status = 0) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := locals, values := [.i32 0] })) :
    wp Project.Beck.«module» ((func35.drop 25).take 15) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  simp only [func35, List.drop, List.take]
  repeat' first
    | wp_run [state.size, state.status, accepted, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
        show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
        ne_eq, not_true_eq_false, not_false_eq_true, List.take, List.drop, List.append_nil, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  exact next

#print axioms computePrepare_exact
#print axioms computeStatus_exact

end Project.Beck.Execution
