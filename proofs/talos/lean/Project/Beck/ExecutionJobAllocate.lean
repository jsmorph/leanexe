import Project.Beck.ExecutionReplicate
import Project.Beck.ExecutionMembership

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def jobBody : Wasm.Program :=
  match (func5[6]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def jobInBounds : Wasm.Program :=
  match (jobBody[14]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def jobEligible : Wasm.Program :=
  match (jobInBounds[34]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

abbrev JobSaved := Fin 43 → Value
abbrev JobAfter := Fin 5 → UInt64

def jobPrefix (saved : JobSaved) : List Value :=
  [saved 0, saved 1, saved 2, saved 3, saved 4, saved 5, saved 6, saved 7, saved 8, saved 9, saved 10, saved 11, saved 12, saved 13, saved 14, saved 15, saved 16, saved 17, saved 18, saved 19, saved 20, saved 21, saved 22, saved 23, saved 24, saved 25, saved 26, saved 27, saved 28, saved 29, saved 30, saved 31, saved 32, saved 33, saved 34, saved 35, saved 36, saved 37, saved 38, saved 39, saved 40, saved 41, saved 42]

def jobReplicateFrame (params : List Value) (saved : JobSaved) (count : Nat)
    (target counter value padding55 padding56 need previous current capacity next result : UInt64)
    (after : JobAfter) : Locals :=
  { params := params
    locals := jobPrefix saved ++
      [.i64 count.toUInt64, .i64 target, .i64 counter, .i64 value, .i64 padding55, .i64 padding56,
        .i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result,
        .i64 (after 0), .i64 (after 1), .i64 (after 2), .i64 (after 3), .i64 (after 4)] }

set_option maxRecDepth 2048 in
theorem job_replicate_shape : (jobEligible.drop 34).take 24 =
    FixedArrayAllocate.program 57 1 ++ [.localGet 62, .localSet 52] ++ UInt64Array.replicateProgram 52 51 53 54 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem jobReplicateAllocated_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : JobSaved) (paramsLength : params.length = 8) (count : Nat)
    (target counter value padding55 padding56 previous current capacity next result : UInt64) (after : JobAfter)
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : count ≤ 56)
    (budget : OutputBudget initial heap (48 + 8 * (count + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (count + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (Array.replicate count value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (jobReplicateFrame params saved count node.root count.toUInt64 value padding55 padding56 need
          previous current capacity next node.root after) env) :
    wp Project.Beck.«module» ((jobEligible.drop 34).take 24 ++ rest) Q initial
      (jobReplicateFrame params saved count target counter value padding55 padding56 (UInt64.ofNat (8 * (count + 1)))
        previous current capacity next result after) env := by
  let need := UInt64.ofNat (8 * (count + 1))
  have needWord : need.toNat = 8 * (count + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  rw [job_replicate_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 57 1 ++ _) Q initial
    (FixedArraySearch.frame params (jobPrefix saved ++
      [.i64 count.toUInt64, .i64 target, .i64 counter, .i64 value, .i64 padding55, .i64 padding56])
      [.i64 (after 0), .i64 (after 1), .i64 (after 2), .i64 (after 3), .i64 (after 4)]
      need previous current capacity next result) env
  apply allocation_exact env initial heap params _ _ 57 (by simp [paramsLength, jobPrefix])
    need previous current capacity next result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous' current' capacity' next'
  simp only [FixedArraySearch.frame, jobPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame [paramsLength]
  apply replicateFinish_owned env initial heap _ 52 51 53 54 count value remaining pageLimit valid bound budget
  all_goals first
    | (solve | simp only [Locals.validIndex, Locals.get, paramsLength, List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, need])
    | (solve | decide)
    | skip
  intro final
  dsimp only
  intro finalValid owned frame finalBudget
  simpa only [jobReplicateFrame, jobPrefix, FixedArrayCopy.counterFrame, Locals.set, List.set, List.length,
    paramsLength, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte, List.cons_append, List.nil_append, need,
    allocatedNode, Nat.toUInt64] using finish final finalValid owned frame finalBudget previous' current' capacity' next'

#print axioms jobReplicateAllocated_owned

end Project.Beck.Execution
