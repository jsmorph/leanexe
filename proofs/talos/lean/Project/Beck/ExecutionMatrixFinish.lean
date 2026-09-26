import Project.Beck.ExecutionMatrixReconstruct

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixInstalledSaved (saved : MatrixSaved) (root : UInt64) (k : Fin 63) : Value :=
  match k.val with
  | 29 | 30 | 31 | 32 => .i64 root
  | _ => saved k

def matrixInstalledAfter (after : MatrixAfter) (root : UInt64) (k : Fin 9) : Value :=
  match k.val with
  | 1 => .i64 0
  | 2 | 3 => .i64 root
  | _ => after k

def matrixInstalledFrame (params : List Value) (saved : MatrixSaved) (source : UInt64) (size : Nat)
    (root value padding79 padding80 need previous current capacity next : UInt64) (after : MatrixAfter) : Locals :=
  matrixPushFrame params (matrixInstalledSaved saved root) source size root size.toUInt64 value padding79 padding80
    need previous current capacity next root (matrixInstalledAfter after root)

def matrixFinishedTail (index size : Nat) (root value padding79 padding80 need previous current capacity next : UInt64)
    (k : Fin 15) : UInt64 :=
  match k.val with
  | 0 => index.toUInt64
  | 1 => 1
  | 2 => (index + 1).toUInt64
  | 3 => (size + 1).toUInt64
  | 4 | 14 => root
  | 5 => size.toUInt64
  | 6 => value
  | 7 => padding79
  | 8 => padding80
  | 9 => need
  | 10 => previous
  | 11 => current
  | 12 => capacity
  | _ => next

theorem matrixRowFrame_post (store : Store Unit) (frame : Locals) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category index : Nat)
    (pointer initialOwner : UInt64) (tail : MatrixTail) (Q : Assertion Unit)
    (next : ∀ saved tail after, Q (.Break 0 store (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer
      category index pointer initialOwner saved tail after)))
    (params : frame.params = matrixParams input point inputOwner inputPointer pointOwner pointPointer)
    (locals : frame.locals.length = 87) (values : frame.values = [])
    (r14 : frame.get 14 = some (.i64 category.toUInt64))
    (r27 : frame.get 27 = some (.i64 pointer)) (r28 : frame.get 28 = some (.i64 pointer))
    (r69 : frame.get 69 = some (.i64 index.toUInt64))
    (r70 : frame.get 70 = some (.i64 input.jobs.toUInt64)) (r71 : frame.get 71 = some (.i64 1))
    (r91 : frame.get 91 = some (.i64 initialOwner))
    (tailReads : ∀ k : Fin 15, frame.get (k.val + 72) = some (.i64 (tail k))) :
    Q (.Break 0 store frame) := by
  rw [matrixRowFrame_reconstruct frame input point inputOwner inputPointer pointOwner pointPointer category index pointer initialOwner
    tail params locals values r14 r27 r28 r69 r70 r71 r91 tailReads]
  exact next _ tail _

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem matrixInstall_exact (env : HostEnv Unit) (initial : Store Unit) (params : List Value) (paramsLength : params.length = 9)
    (saved : MatrixSaved) (source : UInt64) (size : Nat)
    (root value padding79 padding80 need previous current capacity after : UInt64) (suffix : MatrixAfter)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (matrixInstalledFrame params saved source size root value padding79 padding80 need previous current capacity after suffix) env) :
    wp Project.Beck.«module» ((matrixRowBody.drop 104).take 14 ++ rest) Q initial
      (matrixPushFrame params saved source size root size.toUInt64 value padding79 padding80 need previous current capacity after root suffix) env := by
  simp only [matrixRowBody, matrixSelected, matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append, matrixPushFrame, matrixPrefix, matrixSuffix]
  wp_fixed_frame [paramsLength]
  simpa only [matrixInstalledFrame, matrixInstalledSaved, matrixInstalledAfter, matrixPushFrame, matrixPrefix, matrixSuffix,
    List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte] using next

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixFinish_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category index : Nat)
    (source initialOwner : UInt64) (size : Nat) (saved : MatrixSaved)
    (root value padding79 padding80 need previous current capacity after : UInt64) (suffix : MatrixAfter)
    (categoryRead : saved 5 = .i64 category.toUInt64) (indexRead : saved 60 = .i64 index.toUInt64)
    (jobsRead : saved 61 = .i64 input.jobs.toUInt64) (stepRead : saved 62 = .i64 1)
    (ownerRead : suffix 4 = .i64 initialOwner) (indexFit : index + 1 < UInt64.size)
    (Q : Assertion Unit)
    (next : Q (.Break 0 initial (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer
      category (index + 1) root initialOwner (matrixInstalledSaved saved root)
      (matrixFinishedTail index size root value padding79 padding80 need previous current capacity after)
      (matrixInstalledAfter suffix root)))) :
    wp Project.Beck.«module» (matrixRowBody.drop 130) Q initial
      (matrixInstalledFrame (matrixParams input point inputOwner inputPointer pointOwner pointPointer) saved source size
        root value padding79 padding80 need previous current capacity after suffix) env := by
  have guard : ¬UInt64.ofNat index + 1 < UInt64.ofNat index := CheckedNatAdd.guard_of_fits index 1 indexFit
  have increment : UInt64.ofNat index + 1 = (index + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  simp only [matrixRowBody, matrixSelected, matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, matrixInstalledFrame, matrixPushFrame, matrixPrefix, matrixSuffix, matrixInstalledSaved, matrixInstalledAfter,
    matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, categoryRead, indexRead, jobsRead, stepRead, ownerRead]
  wp_fixed_frame [Nat.toUInt64, guard]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa only [guard, reduceIte] using (show ¬(0 : UInt32) ≠ 0 by decide))]
  wp_fixed_frame [List.take, List.drop, List.append_nil, increment]
  simpa only [matrixRowFrame, matrixParams, matrixPrefix, matrixSuffix, matrixTail, matrixRowSaved,
    matrixRowAfter, matrixInstalledSaved, matrixInstalledAfter, matrixFinishedTail, inputValues, pointValues,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceEqDiff, reduceIte, categoryRead, indexRead, jobsRead, stepRead, ownerRead] using next

#print axioms matrixInstall_exact
#print axioms matrixFinish_exact

end Project.Beck.Execution
