import Project.Beck.ExecutionBorderPrepare

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def borderPushedTail (source : UInt64) (size : Nat) (root value padding47 padding48 need previous current capacity next : UInt64)
    (k : Fin 15) : UInt64 :=
  match k.val with
  | 0 => source
  | 1 | 2 | 5 => size.toUInt64
  | 3 => (size + 1).toUInt64
  | 4 | 14 => root
  | 6 => value
  | 7 => padding47
  | 8 => padding48
  | 9 => need
  | 10 => previous
  | 11 => current
  | 12 => capacity
  | _ => next

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem borderInstall_exact (env : HostEnv Unit) (initial : Store Unit) (params : List Value) (paramsLength : params.length = 10)
    (saved : BorderSaved) (columns : Bool) (source : UInt64) (size : Nat)
    (root value padding47 padding48 need previous current capacity after : UInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (borderFrame params (borderInstalledSaved saved columns root)
        (borderPushedTail source size root value padding47 padding48 need previous current capacity after)) env) :
    wp Project.Beck.«module» ((if columns then (borderEligible.drop 148).take 4 else (borderEligible.drop 72).take 4) ++ rest) Q initial
      (borderPushFrame params saved source size root size.toUInt64 value padding47 padding48 need previous current capacity after root) env := by
  cases columns
  all_goals
    simp only [Bool.false_eq_true, reduceIte, borderEligible, func25, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.drop, List.take, List.cons_append, List.nil_append, borderPushFrame, borderPrefix]
    wp_fixed_frame [paramsLength]
    simpa only [borderFrame, borderPrefix, borderTail, borderInstalledSaved, borderPushedTail,
      List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      Bool.false_eq_true, reduceIte, or_false, false_or] using next

#print axioms borderInstall_exact

end Project.Beck.Execution
