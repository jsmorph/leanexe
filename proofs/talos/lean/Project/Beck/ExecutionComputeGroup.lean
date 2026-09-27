import Project.Beck.ExecutionComputeOutputState
import Project.ProofKit.CheckedArrayGet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeGroupProgram : Wasm.Program :=
  [.localGet 57, .localSet 40, .localGet 39, .localSet 42, .localGet 42, .localSet 45,
    .localGet 45, .localSet 60, .localGet 33, .localSet 69, .localGet 40, .localSet 70] ++
  CheckedArrayGet.checkedGetCore 69 70 ++ [.localSet 43, .localGet 43, .call 9] ++ (computeOutputBody.drop 25).take 10

def computeGroupLocals (locals : List Value) (current pointRoot : UInt64) (point : Point) (index : Nat) : List Value :=
  let l := (((locals.set 39 (.i64 index.toUInt64)).set 41 (.i64 current)).set 44 (.i64 current)).set 59 (.i64 current)
  let l := ((l.set 68 (.i64 pointRoot)).set 69 (.i64 index.toUInt64)).set 42 (.i64 point.numerators[index]!)
  (l.set 43 (.i64 (boolWord (negative point.numerators[index]!)))).set 65 (.i64 (Project.Beck.Result.group point index))

set_option maxRecDepth 4096 in
theorem compute_group_shape : (computeOutputBody.drop 4).take 31 = computeGroupProgram := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeGroup_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer current pointRoot : UInt64) (point : Point) (index : Nat) (size : locals.length = 79)
    (indexRead : locals[56]? = some (.i64 index.toUInt64)) (currentRead : locals[38]? = some (.i64 current))
    (pointRead : locals[32]? = some (.i64 pointRoot))
    (represented : UInt64Array.At initial pointRoot point.numerators) (inside : index < point.numerators.size)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := computeGroupLocals locals current pointRoot point index })) :
    wp Project.Beck.«module» ((computeOutputBody.drop 4).take 31) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  rw [compute_group_shape]
  simp only [computeGroupProgram, List.append_assoc, List.cons_append, List.nil_append]
  wp_run [size, indexRead, currentRead, pointRead, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  refine CheckedArrayGet.checkedGetCore_spec 69 70 Project.Beck.«module» env initial _ pointRoot point.numerators index []
    (by simp [Locals.get, size]) (by simp [Locals.get, size]) rfl represented inside Q _ ?_
  wp_run [size, List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  refine wp_call_tw (negative_exact env initial point.numerators[index]) ?_
  rintro final values ⟨same, rfl⟩
  subst final
  cases negativeEq : negative point.numerators[index]
  all_goals
    simp only [computeOutputBody, computeOutput, computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, negativeEq, boolWord, Bool.false_eq_true, reduceIte]
    repeat' first
      | wp_run [size, List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
          show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, List.take, List.drop, List.append_nil, reduceIte]
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
    simpa only [computeGroupLocals, Project.Beck.Result.group, getElem!_pos point.numerators index inside,
      negativeEq, boolWord, Bool.false_eq_true, reduceIte] using next

theorem computeGroup_state {locals : List Value} {jobs overlap index : Nat}
    {initialOwner initialPointer pointRoot original current : UInt64}
    (state : ComputeOutputLocals locals jobs overlap initialOwner initialPointer pointRoot original current index) (point : Point) :
    ComputeOutputLocals (computeGroupLocals locals current pointRoot point index)
      jobs overlap initialOwner initialPointer pointRoot original current index := by
  apply state.preserved
  · simp [computeGroupLocals]
  · unfold computeGroupLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [computeGroupLocals, List.getElem?_set_ne]

#print axioms computeGroup_exact

end Project.Beck.Execution
