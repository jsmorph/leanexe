import Project.Beck.ExecutionJobReadFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def jobCountSaved (members position : Nat) (saved : JobSaved) (index : Fin 43) : Value :=
  if index.val = 8 then .i64 members.toUInt64 else if index.val = 9 then .i64 position.toUInt64 else saved index

def jobCountFrame (count categories members : Nat) (wordsPointer incidencePointer internal : UInt64)
    (state : ParseState) (saved : JobSaved) (tail : JobTail) (rowOwner : UInt64 := incidencePointer) : Locals :=
  jobFrame (rowOwner := rowOwner) count categories wordsPointer incidencePointer internal state (jobCountSaved members (state.position + 1) saved) tail

def jobPreparedSaved (categories members : Nat) (wordsPointer internal : UInt64) (state : ParseState)
    (saved : JobSaved) (index : Fin 43) : Value :=
  match index.val with
  | 8 | 10 => .i64 members.toUInt64
  | 9 | 13 => .i64 (state.position + 1).toUInt64
  | 11 | 12 => .i64 wordsPointer
  | 14 | 15 => .i64 categories.toUInt64
  | _ => jobSaved internal saved index

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem jobPrepareRow_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial : Store Unit) (count categories members : Nat)
    (wordsPointer incidencePointer internal : UInt64) (state : ParseState) (saved : JobSaved) (tail : JobTail)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (jobReplicateFrame (jobParams (rowOwner := rowOwner) count categories wordsPointer incidencePointer state)
        (jobPreparedSaved categories members wordsPointer internal state saved) categories
        (tail 1) (tail 2) 0 (tail 4) (tail 5) (tail 6) (tail 7) (tail 8) (tail 9) (tail 10) (tail 11)
        (fun k => match k.val with | 0 => tail 12 | 1 => tail 13 | 2 => tail 14 | 3 => tail 15 | _ => tail 16)) env) :
    wp Project.Beck.«module» (jobEligible.take 16 ++ rest) Q initial
      (jobCountFrame (rowOwner := rowOwner) count categories members wordsPointer incidencePointer internal state saved tail) env := by
  simp only [jobEligible, jobInBounds, jobBody, func5, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append, jobCountFrame, jobFrame, jobCountSaved, jobParams,
    jobPrefix, jobSaved, jobTail, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte]
  wp_fixed_frame
  simpa only [jobReplicateFrame, jobPreparedSaved, jobParams, jobPrefix, jobSaved,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, or_false, false_or, reduceIte,
    List.cons_append, List.nil_append] using next

#print axioms jobPrepareRow_exact

end Project.Beck.Execution
