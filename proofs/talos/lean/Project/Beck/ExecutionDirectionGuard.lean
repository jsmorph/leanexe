import Project.Beck.ExecutionDirectionReplicate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionGuard_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (free : Nat) (size : locals.length = 112) (jobsBound : input.jobs ≤ 6) (available : free < input.jobs)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := (locals.set 45 (.i64 free.toUInt64)).set 46 (.i64 free.toUInt64), values := [.i32 0] })) :
    wp Project.Beck.«module» ((func30.drop 275).take 13) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := locals, values := [.i64 free.toUInt64] } env := by
  have jobsFit : input.jobs < UInt64.size := by change input.jobs < 18446744073709551616; omega
  have freeFit : free < UInt64.size := available.trans jobsFit
  have different : free.toUInt64 ≠ input.jobs.toUInt64 := by
    intro equal
    have equality := congrArg UInt64.toNat equal
    rw [UInt64.toNat_ofNat_of_lt' freeFit, UInt64.toNat_ofNat_of_lt' jobsFit] at equality
    omega
  simp only [func30, List.drop, List.take]
  repeat' first
    | (wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
        size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, different,
        show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
        ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  exact next

set_option maxRecDepth 4096 in
theorem directionEligiblePrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (size : locals.length = 112) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := ((locals.set 48 (.i64 input.jobs.toUInt64)).set 89 (.i64 input.jobs.toUInt64)).set 92 (.i64 0) })) :
    wp Project.Beck.«module» (directionEligible.take 6) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  simp only [directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

#print axioms directionGuard_exact
#print axioms directionEligiblePrepare_exact

end Project.Beck.Execution
