import Project.Beck.ExecutionRoundPush
import Project.ProofKit.CheckedArrayGet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundNumeratorProgram : Wasm.Program :=
  [.localGet 63, .localSet 47, .localGet 46, .localSet 49, .localGet 49, .localSet 50,
    .localGet 50, .localSet 66, .localGet 8, .localSet 75, .localGet 47, .localSet 76] ++
  CheckedArrayGet.checkedGetCore 75 76 ++
  [.localGet 39, .mulI64, .localGet 38, .localGet 21, .localSet 75, .localGet 47, .localSet 76] ++
  CheckedArrayGet.checkedGetCore 75 76 ++ [.mulI64, .addI64, .localSet 72]

def roundNumeratorLocals (locals : List Value) (current pointPointer directionPointer : UInt64)
    (index : Nat) (value : UInt64) : List Value :=
  let l := (((locals.set 38 (.i64 index.toUInt64)).set 40 (.i64 current)).set 41 (.i64 current)).set 57 (.i64 current)
  let l := ((l.set 66 (.i64 pointPointer)).set 67 (.i64 index.toUInt64)).set 66 (.i64 directionPointer)
  (l.set 67 (.i64 index.toUInt64)).set 63 (.i64 value)

set_option maxRecDepth 4096 in
theorem round_numerator_shape : (roundBody.drop 4).take 34 = roundNumeratorProgram := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundNumerator_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (d : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer directionPointer current stepNumerator stepDenominator : UInt64)
    (index : Nat) (size : locals.length = 77)
    (indexRead : locals[54]? = some (.i64 index.toUInt64)) (currentRead : locals[37]? = some (.i64 current))
    (directionRead : locals[12]? = some (.i64 directionPointer))
    (numeratorRead : locals[29]? = some (.i64 stepNumerator)) (denominatorRead : locals[30]? = some (.i64 stepDenominator))
    (pointAt : UInt64Array.At initial pointPointer point.numerators) (directionAt : UInt64Array.At initial directionPointer d)
    (pointBound : index < point.numerators.size) (directionBound : index < d.size)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := roundNumeratorLocals locals current pointPointer directionPointer index
          (point.numerators[index] * stepDenominator + stepNumerator * d[index]) })) :
    wp Project.Beck.«module» ((roundBody.drop 4).take 34) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  rw [round_numerator_shape]
  simp only [roundNumeratorProgram, List.append_assoc, List.cons_append, List.nil_append]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, indexRead, currentRead, reduceIte]
  refine CheckedArrayGet.checkedGetCore_spec 75 76 Project.Beck.«module» env initial _ pointPointer point.numerators index []
    (by simp [Locals.get, size]) (by simp [Locals.get, size]) rfl pointAt pointBound Q _ ?_
  wp_run [size, List.length_cons, List.length_nil, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, numeratorRead, denominatorRead, directionRead, reduceIte]
  refine CheckedArrayGet.checkedGetCore_spec 75 76 Project.Beck.«module» env initial _ directionPointer d index
    [.i64 stepNumerator, .i64 (point.numerators[index] * stepDenominator)]
    (by simp [Locals.get, size]) (by simp [Locals.get, size]) rfl directionAt directionBound Q _ ?_
  wp_run [size, List.length_cons, List.length_nil, List.length_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  exact next

#print axioms roundNumerator_exact

end Project.Beck.Execution
