import Project.Beck.ExecutionDirectionBasis
import Project.Beck.ExecutionFree

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionFreeLocals (locals : List Value) (input : Input) (point : Point) (basis : Basis)
    (inputOwner inputPointer pointOwner pointPointer ro rp co cp : UInt64) : List Value :=
  let l := ((((locals.set 28 (.i64 basis.determinant)).set 27 (.i64 cp)).set 26 (.i64 co)).set 25 (.i64 rp)).set 24 (.i64 ro)
  let l := ((((l.set 29 (.i64 ro)).set 30 (.i64 rp)).set 31 (.i64 co)).set 32 (.i64 cp)).set 33 (.i64 basis.determinant)
  let l := (((l.set 34 (.i64 input.status)).set 35 (.i64 input.jobs.toUInt64)).set 36 (.i64 input.categories.toUInt64)).set 37 (.i64 input.overlap.toUInt64)
  let l := (((l.set 38 (.i64 inputOwner)).set 39 (.i64 inputPointer)).set 40 (.i64 point.denominator)).set 41 (.i64 pointOwner)
  ((l.set 42 (.i64 pointPointer)).set 43 (.i64 co)).set 44 (.i64 cp)

set_option maxRecDepth 4096 in
theorem directionFreePrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (inputOwner inputPointer pointOwner pointPointer ro rp co cp : UInt64)
    (size : locals.length = 112) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := directionFreeLocals locals input point basis inputOwner inputPointer pointOwner pointPointer ro rp co cp
        values := [.i64 cp, .i64 co] ++ pointValues point pointOwner pointPointer ++ inputValues input inputOwner inputPointer })) :
    wp Project.Beck.«module» ((func30.drop 226).take 48) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := locals, values := basisValues basis ro rp co cp } env := by
  simp only [func30, List.drop, List.take]
  wp_run [matrixParams, inputValues, pointValues, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_free_shape : (func30.drop 226).take 49 = (func30.drop 226).take 48 ++ [.call 28] := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionFree_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (inputOwner inputPointer pointOwner pointPointer ro rp co cp : UInt64)
    (size : locals.length = 112) (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (columnsArray : UInt64Array.At initial cp basis.columns) (pointSize : input.jobs ≤ point.numerators.size)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := directionFreeLocals locals input point basis inputOwner inputPointer pointOwner pointPointer ro rp co cp
        values := [.i64 (freeColumn input point basis.columns).toUInt64] })) :
    wp Project.Beck.«module» ((func30.drop 226).take 49) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := locals, values := basisValues basis ro rp co cp } env := by
  rw [direction_free_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
      locals := directionFreeLocals locals input point basis inputOwner inputPointer pointOwner pointPointer ro rp co cp
      values := [.i64 cp, .i64 co] ++ pointValues point pointOwner pointPointer ++ inputValues input inputOwner inputPointer })
  · exact directionFreePrepare_exact env initial locals input point basis inputOwner inputPointer pointOwner pointPointer ro rp co cp size _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  refine wp_call_tw (freeColumn_exact env initial input point basis.columns inputOwner inputPointer pointOwner pointPointer co cp pointArray columnsArray pointSize) ?_
  rintro final values ⟨rfl, rfl⟩
  rw [wp_nil]
  exact next

#print axioms directionFree_exact

end Project.Beck.Execution
