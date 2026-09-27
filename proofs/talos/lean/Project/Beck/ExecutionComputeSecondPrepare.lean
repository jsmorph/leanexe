import Project.Beck.ExecutionComputePrepare

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def computeSecondPreparedLocals (locals : List Value) (jobs : Nat) : List Value :=
  ((locals.set 22 (.i64 jobs.toUInt64)).set 56 (.i64 jobs.toUInt64)).set 59 (.i64 0)

set_option maxRecDepth 4096 in
theorem computeSecondPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer : UInt64) (jobs : Nat) (size : locals.length = 79)
    (jobsRead : locals[9]? = some (.i64 jobs.toUInt64)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := computeSecondPreparedLocals locals jobs })) :
    wp Project.Beck.«module» ((computeAccepted.drop 68).take 6) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  simp only [computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop]
  wp_run [size, jobsRead, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

theorem computeSecondPrepared_keeps (locals : List Value) (jobs k : Nat) (bound : k < 56) (different : k ≠ 22) :
    (computeSecondPreparedLocals locals jobs)[k]? = locals[k]? := by
  simp only [computeSecondPreparedLocals, List.getElem?_set_ne (by omega : 59 ≠ k),
    List.getElem?_set_ne (by omega : 56 ≠ k), List.getElem?_set_ne different.symm]

#print axioms computeSecondPrepare_exact

end Project.Beck.Execution
