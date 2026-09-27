import Project.Beck.ExecutionRoundStart
import Project.Beck.ExecutionBoundary

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundBoundaryPrepared (locals : List Value) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer directionRoot : UInt64) : List Value :=
  let l := (((locals.set 14 (.i64 input.status)).set 15 (.i64 input.jobs.toUInt64)).set 16 (.i64 input.categories.toUInt64)).set 17 (.i64 input.overlap.toUInt64)
  let l := (((l.set 18 (.i64 inputOwner)).set 19 (.i64 inputPointer)).set 20 (.i64 point.denominator)).set 21 (.i64 pointOwner)
  ((l.set 22 (.i64 pointPointer)).set 23 (.i64 directionRoot)).set 24 (.i64 directionRoot)

def roundBoundaryLocals (locals : List Value) (step : UInt64 × UInt64) : List Value :=
  (((((locals.set 26 (.i64 step.2)).set 25 (.i64 step.1)).set 27 (.i64 step.1)).set 28 (.i64 step.2)).set 29 (.i64 step.1)).set 30 (.i64 step.2)

set_option maxRecDepth 4096 in
theorem roundBoundaryPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64)
    (size : locals.length = 77) (ownerRead : locals[11]? = some (.i64 root)) (pointerRead : locals[12]? = some (.i64 root))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := roundBoundaryPrepared locals input point inputOwner inputPointer pointOwner pointPointer root
        values := (boundaryParams input point inputOwner inputPointer pointOwner pointPointer root root).reverse })) :
    wp Project.Beck.«module» (roundUsable.take 33) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  simp only [roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem roundBoundaryResult_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (step : UInt64 × UInt64) (paramsSize : params.length = 9) (size : locals.length = 77) (nonzero : step.2 ≠ 0)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := roundBoundaryLocals locals step, values := [.i32 0] })) :
    wp Project.Beck.«module» ((roundUsable.drop 34).take 20) Q initial
      { params := params, locals := locals, values := [.i64 step.2, .i64 step.1] } env := by
  simp only [roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  repeat' first
    | wp_run [paramsSize, size, List.length_set, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, nonzero,
        show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide,
        show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true,
        List.take, List.drop, List.append_nil, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  exact next

set_option maxRecDepth 4096 in
theorem round_boundary_shape : roundUsable.take 54 = roundUsable.take 33 ++ (.call 32 :: (roundUsable.drop 34).take 20) := rfl

set_option maxRecDepth 4096 in
theorem roundBoundary_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (d : Array UInt64) (inputOwner inputPointer pointOwner pointPointer root : UInt64)
    (size : locals.length = 77) (ownerRead : locals[11]? = some (.i64 root)) (pointerRead : locals[12]? = some (.i64 root))
    (pointAt : UInt64Array.At initial pointPointer point.numerators) (directionAt : UInt64Array.At initial root d)
    (pointSize : input.jobs ≤ point.numerators.size) (directionSize : input.jobs ≤ d.size)
    (nonzero : (boundaryStep input point d).2 ≠ 0) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := roundBoundaryLocals (roundBoundaryPrepared locals input point inputOwner inputPointer pointOwner pointPointer root) (boundaryStep input point d),
        values := [.i32 0] })) :
    wp Project.Beck.«module» (roundUsable.take 54) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let prepared := roundBoundaryPrepared locals input point inputOwner inputPointer pointOwner pointPointer root
  have preparedSize : prepared.length = 77 := by simp [prepared, roundBoundaryPrepared, size]
  rw [round_boundary_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame =
    { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := prepared,
      values := (boundaryParams input point inputOwner inputPointer pointOwner pointPointer root root).reverse })
  · exact roundBoundaryPrepare_exact env initial locals input point inputOwner inputPointer pointOwner pointPointer root size ownerRead pointerRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_call_tw (boundaryStep_exact env initial input point d inputOwner inputPointer pointOwner pointPointer root root
    pointAt directionAt pointSize directionSize) ?_
  rintro final values ⟨same, rfl⟩
  subst final
  exact roundBoundaryResult_exact env initial _ prepared (boundaryStep input point d)
    (by simp [matrixParams, inputValues, pointValues]) preparedSize nonzero Q next

#print axioms roundBoundary_exact

end Project.Beck.Execution
