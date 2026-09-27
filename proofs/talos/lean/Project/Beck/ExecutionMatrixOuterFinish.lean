import Project.Beck.ExecutionMatrixOuterFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixOuterFinishedSaved (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (pointer owner : UInt64)
    (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 3 | 4 => .i64 pointer
  | 39 => .i64 input.status
  | 40 => .i64 input.jobs.toUInt64
  | 41 => .i64 input.categories.toUInt64
  | 42 => .i64 input.overlap.toUInt64
  | 43 => .i64 inputOwner
  | 44 => .i64 inputPointer
  | 45 => .i64 point.denominator
  | 46 => .i64 pointOwner
  | 47 => .i64 pointPointer
  | 48 | 60 => .i64 category.toUInt64
  | 49 => .i64 0
  | 57 | 62 => .i64 (category + 1).toUInt64
  | 61 => .i64 1
  | _ => matrixBranchSaved input category pointer owner saved k

def matrixOuterFinishedAfter (pointer : UInt64) (after : MatrixAfter) (k : Fin 11) : Value :=
  match k.val with
  | 6 => .i64 0
  | 7 | 8 => .i64 pointer
  | _ => after k

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixOuterFinish_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (pointer owner : UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (categoryBound : category < input.categories)
    (Q : Assertion Unit)
    (next : ∀ saved tail after, Q (.Break 0 initial
      (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer (category + 1) pointer owner saved tail after))) :
    wp Project.Beck.«module» (matrixBody.drop 44) Q initial
      (matrixBranchFrame input point inputOwner inputPointer pointOwner pointPointer category pointer owner saved tail after) env := by
  have fit : category + 1 < UInt64.size := by change category + 1 < 18446744073709551616; omega
  have guard : ¬UInt64.ofNat category + 1 < UInt64.ofNat category := CheckedNatAdd.guard_of_fits category 1 fit
  have increment : UInt64.ofNat category + 1 = UInt64.ofNat (category + 1) := (UInt64.ofNat_add _ _).symm
  have incrementGuard : ¬UInt64.ofNat (category + 1) < UInt64.ofNat category := by rw [← increment]; exact guard
  have counter := liveCount_exact env initial input point inputOwner inputPointer pointOwner pointPointer category
    pointArray inputArray pointSize inputSize jobs categories categoryBound
  simp only [matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop,
    matrixBranchFrame, matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix, matrixBranchSaved,
    inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
  wp_fixed_frame
  refine wp_call_tw (counter.append_args rfl rfl rfl [.i64 input.overlap.toUInt64]) ?_
  rintro final values ⟨out, rfl, same, rfl⟩
  subst final
  simp only [List.cons_append, List.nil_append, List.append_nil]
  by_cases selected : input.overlap.toUInt64 < (liveCount input point category).toUInt64
  all_goals
    repeat' first
      | wp_fixed_frame_step
      | ((first
          | rw [wp_ltUI64_cons] | rw [wp_neI64_cons] | rw [wp_constI64_cons] | rw [wp_const_cons]
          | rw [wp_addI64_cons] | rw [wp_localTee_cons] | rw [wp_br_if_cons] | rw [wp_br_cons] | rw [wp_nil]) <;>
          simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
            List.take, List.drop, List.append_nil, Nat.toUInt64, selected, guard, increment, incrementGuard,
            ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
    wp_fixed_frame [guard, increment, incrementGuard]
    simpa only [matrixOuterFrame, matrixPlainFrame, matrixOuterSaved, matrixOuterFinishedSaved, matrixOuterFinishedAfter,
      matrixBranchSaved, matrixParams, matrixPrefix, matrixTail, matrixSuffix, inputValues, pointValues,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, Nat.reduceEqDiff, Nat.toUInt64, reduceIte] using
      next (matrixOuterFinishedSaved input point inputOwner inputPointer pointOwner pointPointer category pointer owner saved)
        tail (matrixOuterFinishedAfter pointer after)

#print axioms matrixOuterFinish_exact

end Project.Beck.Execution
