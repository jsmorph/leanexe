import Project.Beck.ExecutionJobState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def jobInstalledSaved (categories : Nat) (wordsPointer internal root : UInt64) (nextState : ParseState)
    (saved : JobSaved) (index : Fin 43) : Value :=
  match index.val with
  | 23 | 30 => .i64 nextState.position.toUInt64
  | 24 | 31 => .i64 nextState.overlap.toUInt64
  | 25 | 26 | 32 | 33 => .i64 root
  | 27 | 28 => .i64 wordsPointer
  | 29 => .i64 categories.toUInt64
  | _ => jobSaved internal saved index

def jobInstalledFrame (count categories : Nat) (wordsPointer internal : UInt64) (state nextState : ParseState)
    (saved : JobSaved) (leftPointer rightPointer : UInt64) (leftSize rightSize : Nat)
    (root padding60 padding61 need previous current capacity next : UInt64) (rowOwner : UInt64 := leftPointer) : Locals :=
  jobAppendFrame (jobParams (rowOwner := rowOwner) count categories wordsPointer leftPointer state)
    (jobInstalledSaved categories wordsPointer internal root nextState saved) leftPointer rightPointer leftSize rightSize
    root rightSize.toUInt64 padding60 padding61 need previous current capacity next root

def jobAppendedTail (leftPointer rightPointer : UInt64) (leftSize rightSize : Nat)
    (root padding60 padding61 need previous current capacity next : UInt64) (index : Fin 17) : UInt64 :=
  match index.val with
  | 0 => leftPointer
  | 1 => rightPointer
  | 2 | 5 => leftSize.toUInt64
  | 3 | 6 | 8 => rightSize.toUInt64
  | 4 => (leftSize + rightSize).toUInt64
  | 7 | 16 => root
  | 9 => padding60
  | 10 => padding61
  | 11 => need
  | 12 => previous
  | 13 => current
  | 14 => capacity
  | _ => next

theorem jobFrame_post {rowOwner : UInt64} (store : Store Unit) (frame : Locals) (count categories : Nat)
    (wordsPointer rowPointer internal : UInt64) (state : ParseState) (tail : JobTail)
    (Q : Assertion Unit)
    (next : ∀ saved tail, Q (.Fallthrough store (jobFrame (rowOwner := rowOwner) count categories wordsPointer rowPointer internal state saved tail)))
    (params : frame.params = jobParams (rowOwner := rowOwner) count categories wordsPointer rowPointer state)
    (locals : frame.locals.length = 60) (values : frame.values = [])
    (r8 : frame.get 8 = some (.i64 internal)) (r9 : frame.get 9 = some (.i64 0)) (r15 : frame.get 15 = some (.i64 0))
    (tailReads : ∀ index : Fin 17, frame.get (index.val + 51) = some (.i64 (tail index))) :
    Q (.Fallthrough store frame) := by
  rw [jobFrame_reconstruct frame count categories wordsPointer rowPointer internal state tail params locals values r8 r9 r15 tailReads]
  exact next _ tail

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem jobFinish_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial : Store Unit) (count categories : Nat)
    (wordsPointer internal : UInt64) (state nextState : ParseState) (saved : JobSaved)
    (leftPointer rightPointer : UInt64) (leftSize rightSize : Nat)
    (root padding60 padding61 need previous current capacity after : UInt64)
    (ownerNonzero : wordsPointer ≠ 0) (ownerDifferent : wordsPointer ≠ internal)
    (Q : Assertion Unit)
    (next : ∀ saved tail, Q (.Fallthrough initial (jobFrame count categories wordsPointer root root nextState saved tail))) :
    wp Project.Beck.«module» (jobAccepted.drop 119) Q initial
      (jobInstalledFrame (rowOwner := rowOwner) (count + 1) categories wordsPointer internal state nextState saved leftPointer rightPointer leftSize rightSize
        root padding60 padding61 need previous current capacity after) env := by
  have decrement : (count + 1).toUInt64 - 1 = count.toUInt64 := by
    rw [Nat.toUInt64, UInt64.ofNat_add]
    exact UInt64.add_sub_cancel _ _
  simp only [jobAccepted, jobEligible, jobInBounds, jobBody, func5, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop, jobInstalledFrame, jobAppendFrame,
    jobInstalledSaved, jobSaved, jobPrefix, jobParams,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte,
    List.cons_append, List.nil_append]
  repeat' ((try wp_fixed_frame [ownerNonzero, ownerDifferent, List.take, List.drop, List.append_nil, decrement]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  wp_fixed_frame [ownerNonzero, ownerDifferent, List.take, List.drop, List.append_nil, decrement]
  apply jobFrame_post initial _ count categories wordsPointer root root nextState
    (jobAppendedTail leftPointer rightPointer leftSize rightSize root padding60 padding61 need previous current capacity after) Q next
  all_goals first | rfl | (intro index; fin_cases index <;> rfl)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem jobInstall_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial : Store Unit) (count categories : Nat)
    (wordsPointer internal : UInt64) (state nextState : ParseState) (saved : JobSaved)
    (leftPointer rightPointer : UInt64) (leftSize rightSize : Nat)
    (root padding60 padding61 need previous current capacity after : UInt64)
    (positionRead : saved 23 = .i64 nextState.position.toUInt64) (overlapRead : saved 24 = .i64 nextState.overlap.toUInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (jobInstalledFrame (rowOwner := rowOwner) count categories wordsPointer internal state nextState saved leftPointer rightPointer leftSize rightSize
        root padding60 padding61 need previous current capacity after) env) :
    wp Project.Beck.«module» ((jobAccepted.drop 86).take 18 ++ rest) Q initial
      (jobAppendFrame (jobParams (rowOwner := rowOwner) count categories wordsPointer leftPointer state) (jobSaved internal saved)
        leftPointer rightPointer leftSize rightSize root rightSize.toUInt64 padding60 padding61 need previous current capacity after root) env := by
  simp only [jobAccepted, jobEligible, jobInBounds, jobBody, func5, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop, List.take, List.cons_append, List.nil_append,
    jobAppendFrame, jobParams, jobPrefix, jobSaved,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte, positionRead, overlapRead]
  wp_fixed_frame
  simpa only [jobInstalledFrame, jobAppendFrame, jobInstalledSaved, jobPrefix, jobParams, jobSaved,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte,
    List.cons_append, List.nil_append, positionRead, overlapRead] using next

#print axioms jobFinish_exact
#print axioms jobInstall_exact

end Project.Beck.Execution
