import Project.Beck.ExecutionMatrix
import Project.Beck.ExecutionFindBasis

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionPreparedLocals (locals : List Value) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) : List Value :=
  let l := (((locals.set 0 (.i64 input.status)).set 1 (.i64 input.jobs.toUInt64)).set 2 (.i64 input.categories.toUInt64)).set 3 (.i64 input.overlap.toUInt64)
  let l := (((l.set 4 (.i64 inputOwner)).set 5 (.i64 inputPointer)).set 6 (.i64 point.denominator)).set 7 (.i64 pointOwner)
  l.set 8 (.i64 pointPointer)

def directionMatrixLocals (locals : List Value) (jobs : Nat) (root : UInt64) : List Value :=
  let l := (((locals.set 10 (.i64 root)).set 9 (.i64 root)).set 11 (.i64 root)).set 12 (.i64 root)
  (((l.set 13 (.i64 jobs.toUInt64)).set 14 (.i64 jobs.toUInt64)).set 15 (.i64 root)).set 16 (.i64 root)

set_option maxRecDepth 4096 in
theorem directionPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (size : locals.length = 112) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := directionPreparedLocals locals input point inputOwner inputPointer pointOwner pointPointer
        values := pointValues point pointOwner pointPointer ++ inputValues input inputOwner inputPointer })) :
    wp Project.Beck.«module» (func30.take 27) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  simp only [func30, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem directionMatrixResult_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64)
    (size : locals.length = 112) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := directionMatrixLocals locals input.jobs root })) :
    wp Project.Beck.«module» ((func30.drop 28).take 14) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := locals, values := [.i64 root, .i64 root] } env := by
  simp only [func30, List.drop, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_start_shape : func30.take 42 = func30.take 27 ++ (.call 19 :: (func30.drop 28).take 14) := rfl

set_option maxRecDepth 4096 in
theorem directionStart_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (locals : List Value) (size : locals.length = 112) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (56 + 448 * input.jobs * input.categories + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node (protectedMatrix input point) →
      heap.Frame initial finalHeap final → FreshFor heap node → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
          locals := directionMatrixLocals (directionPreparedLocals locals input point inputOwner inputPointer pointOwner pointPointer) input.jobs node.root })) :
    wp Project.Beck.«module» (func30.take 42) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  let prepared := directionPreparedLocals locals input point inputOwner inputPointer pointOwner pointPointer
  have preparedSize : prepared.length = 112 := by simp [prepared, directionPreparedLocals, size]
  rw [direction_start_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := params, locals := prepared, values := pointValues point pointOwner pointPointer ++ inputValues input inputOwner inputPointer })
  · exact directionPrepare_exact env initial locals input point inputOwner inputPointer pointOwner pointPointer size _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  refine wp_call_tw (protectedMatrix_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer
    remaining pageLimit valid pointArray pointProtected inputArray inputProtected pointSize inputSize jobs categories overlap budget) ?_
  rintro final values ⟨finalHeap, node, rfl, finalValid, owned, preserved, fresh, finalBudget⟩
  exact directionMatrixResult_exact env final prepared input point inputOwner inputPointer pointOwner pointPointer node.root preparedSize _
    (next final finalHeap node finalValid owned preserved fresh finalBudget)

#print axioms directionStart_exact

end Project.Beck.Execution
