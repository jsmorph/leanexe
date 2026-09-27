import Project.Beck.ExecutionPush
import Project.Beck.ExecutionMemberCapacity

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def borderEligible : Wasm.Program :=
  match (func25[21]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

abbrev BorderSaved := Fin 30 → Value

def borderPrefix (saved : BorderSaved) : List Value :=
  [saved 0, saved 1, saved 2, saved 3, saved 4, saved 5, saved 6, saved 7, saved 8, saved 9, saved 10, saved 11, saved 12, saved 13, saved 14, saved 15, saved 16, saved 17, saved 18, saved 19, saved 20, saved 21, saved 22, saved 23, saved 24, saved 25, saved 26, saved 27, saved 28, saved 29]

def borderPushFrame (params : List Value) (saved : BorderSaved) (source : UInt64) (size : Nat)
    (target counter value padding47 padding48 need previous current capacity next result : UInt64) : Locals :=
  { params := params
    locals := borderPrefix saved ++
      [.i64 source, .i64 size.toUInt64, .i64 size.toUInt64, .i64 (size + 1).toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding47, .i64 padding48,
        .i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result] }

set_option maxRecDepth 2048 in
theorem border_push_shape : (borderEligible.drop 36).take 36 =
    FixedArrayAllocate.program 49 1 ++ [.localGet 54, .localSet 44] ++ pushFinishProgram 40 44 43 42 41 45 46 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem borderPushAllocated_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : BorderSaved) (paramsLength : params.length = 10)
    (pointer : UInt64) (words : Array UInt64) (value : UInt64)
    (target counter padding47 padding48 previous current capacity next result : UInt64)
    (remaining pageLimit : Nat) (represented : UInt64Array.At initial pointer words)
    (protectedWords : heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size < 56)
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (words.size + 2))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (words.push value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (borderPushFrame params saved pointer words.size node.root words.size.toUInt64 value padding47 padding48
          need previous current capacity next node.root) env) :
    wp Project.Beck.«module» ((borderEligible.drop 36).take 36 ++ rest) Q initial
      (borderPushFrame params saved pointer words.size target counter value padding47 padding48
        (UInt64.ofNat (8 * (words.size + 2))) previous current capacity next result) env := by
  let need := UInt64.ofNat (8 * (words.size + 2))
  have needWord : need.toNat = 8 * (words.size + 2) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  rw [border_push_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 49 1 ++ _) Q initial
    (FixedArraySearch.frame params (borderPrefix saved ++
      [.i64 pointer, .i64 words.size.toUInt64, .i64 words.size.toUInt64, .i64 (words.size + 1).toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding47, .i64 padding48]) []
      need previous current capacity next result) env
  apply allocation_exact env initial heap params _ _ 49 (by simp [paramsLength, borderPrefix])
    need previous current capacity next result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous' current' capacity' next'
  simp only [FixedArraySearch.frame, borderPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame [paramsLength]
  apply pushFinish_owned env initial heap _ 40 44 43 42 41 45 46 pointer words value remaining pageLimit
    represented protectedWords valid (by omega) budget
  all_goals first
    | (solve | simp only [Locals.validIndex, Locals.get, paramsLength, List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, need])
    | (solve | decide)
    | skip
  intro final
  dsimp only
  intro finalValid owned frame finalBudget
  simpa only [borderPushFrame, borderPrefix, FixedArrayCopy.counterFrame, Locals.set, List.set, List.length,
    paramsLength, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte, List.cons_append, List.nil_append, need,
    allocatedNode, Nat.toUInt64] using finish final finalValid owned frame finalBudget previous' current' capacity' next'

#print axioms borderPushAllocated_owned

end Project.Beck.Execution
