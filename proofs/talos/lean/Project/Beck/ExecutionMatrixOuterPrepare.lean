import Project.Beck.ExecutionMatrixOuterFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixPreparedSaved (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (pointer owner : UInt64)
    (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 5 | 17 => .i64 category.toUInt64
  | 6 | 7 => .i64 pointer
  | 8 => .i64 input.status
  | 9 => .i64 input.jobs.toUInt64
  | 10 => .i64 input.categories.toUInt64
  | 11 => .i64 input.overlap.toUInt64
  | 12 => .i64 inputOwner
  | 13 => .i64 inputPointer
  | 14 => .i64 point.denominator
  | 15 => .i64 pointOwner
  | 16 => .i64 pointPointer
  | _ => matrixOuterSaved input category pointer owner saved k

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixOuterPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (pointer owner : UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (categoryBound : category < input.categories)
    (overlap : input.overlap ≤ 8)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      { matrixPlainFrame input point inputOwner inputPointer pointOwner pointPointer
          (matrixPreparedSaved input point inputOwner inputPointer pointOwner pointPointer category pointer owner saved) tail after
        with values := [.i32 (if input.overlap < liveCount input point category then 1 else 0)] } env) :
    wp Project.Beck.«module» ((matrixBody.drop 4).take 39 ++ rest) Q initial
      (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer category pointer owner saved tail after) env := by
  have countBound : liveCount input point category ≤ input.jobs := by
    simpa only [countPrefix_total] using countPrefix_le input point category input.jobs
  have overlapFit : input.overlap < UInt64.size := by change input.overlap < 18446744073709551616; omega
  have countFit : liveCount input point category < UInt64.size := by
    change liveCount input point category < 18446744073709551616; omega
  have compare : input.overlap.toUInt64 < (liveCount input point category).toUInt64 ↔ input.overlap < liveCount input point category := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' overlapFit, UInt64.toNat_ofNat_of_lt' countFit]
  have counter := liveCount_exact env initial input point inputOwner inputPointer pointOwner pointPointer category
    pointArray inputArray pointSize inputSize jobs categories categoryBound
  simp only [matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take,
    List.cons_append, List.nil_append, matrixOuterFrame, matrixPlainFrame, matrixParams, matrixPrefix, matrixTail,
    matrixSuffix, matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
  wp_fixed_frame
  refine wp_call_tw (counter.append_args rfl rfl rfl [.i64 input.overlap.toUInt64]) ?_
  rintro final values ⟨out, rfl, same, rfl⟩
  subst final
  simp only [List.cons_append, List.nil_append, List.append_nil]
  wp_fixed_frame [compare]
  simpa only [matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix, matrixPreparedSaved, matrixOuterSaved,
    inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte] using next

#print axioms matrixOuterPrepare_exact

end Project.Beck.Execution
