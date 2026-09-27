import Project.Beck.ExecutionPush
import Project.Beck.ExecutionMemberCapacity

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def matrixBody : Wasm.Program :=
  match (func19[53]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def matrixSelected : Wasm.Program :=
  match (matrixBody[43]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def matrixRowBody : Wasm.Program :=
  match (matrixSelected[12]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

abbrev MatrixSaved := Fin 63 → Value
abbrev MatrixAfter := Fin 11 → Value

def matrixPrefix (saved : MatrixSaved) : List Value :=
  [saved 0, saved 1, saved 2, saved 3, saved 4, saved 5, saved 6, saved 7, saved 8, saved 9, saved 10, saved 11, saved 12, saved 13, saved 14, saved 15, saved 16, saved 17, saved 18, saved 19, saved 20, saved 21, saved 22, saved 23, saved 24, saved 25, saved 26, saved 27, saved 28, saved 29, saved 30, saved 31, saved 32, saved 33, saved 34, saved 35, saved 36, saved 37, saved 38, saved 39, saved 40, saved 41, saved 42, saved 43, saved 44, saved 45, saved 46, saved 47, saved 48, saved 49, saved 50, saved 51, saved 52, saved 53, saved 54, saved 55, saved 56, saved 57, saved 58, saved 59, saved 60, saved 61, saved 62]

def matrixSuffix (after : MatrixAfter) : List Value :=
  [after 0, after 1, after 2, after 3, after 4, after 5, after 6, after 7, after 8, after 9, after 10]

def matrixPushFrame (params : List Value) (saved : MatrixSaved) (source : UInt64) (size : Nat)
    (target counter value padding79 padding80 need previous current capacity next result : UInt64)
    (after : MatrixAfter) : Locals :=
  { params := params
    locals := matrixPrefix saved ++
      [.i64 source, .i64 size.toUInt64, .i64 size.toUInt64, .i64 (size + 1).toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding79, .i64 padding80,
        .i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result] ++ matrixSuffix after }

set_option maxRecDepth 2048 in
theorem matrix_push_shape : (matrixRowBody.drop 68).take 36 =
    FixedArrayAllocate.program 81 1 ++ [.localGet 86, .localSet 76] ++ pushFinishProgram 72 76 75 74 73 77 78 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixPushAllocated_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : MatrixSaved) (paramsLength : params.length = 9)
    (pointer : UInt64) (words : Array UInt64) (value : UInt64)
    (target counter padding79 padding80 previous current capacity next result : UInt64) (after : MatrixAfter)
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
        (matrixPushFrame params saved pointer words.size node.root words.size.toUInt64 value padding79 padding80
          need previous current capacity next node.root after) env) :
    wp Project.Beck.«module» ((matrixRowBody.drop 68).take 36 ++ rest) Q initial
      (matrixPushFrame params saved pointer words.size target counter value padding79 padding80
        (UInt64.ofNat (8 * (words.size + 2))) previous current capacity next result after) env := by
  let need := UInt64.ofNat (8 * (words.size + 2))
  have needWord : need.toNat = 8 * (words.size + 2) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  rw [matrix_push_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 81 1 ++ _) Q initial
    (FixedArraySearch.frame params (matrixPrefix saved ++
      [.i64 pointer, .i64 words.size.toUInt64, .i64 words.size.toUInt64, .i64 (words.size + 1).toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding79, .i64 padding80]) (matrixSuffix after)
      need previous current capacity next result) env
  apply allocation_exact env initial heap params _ _ 81 (by simp [paramsLength, matrixPrefix])
    need previous current capacity next result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous' current' capacity' next'
  simp only [FixedArraySearch.frame, matrixPrefix, matrixSuffix, List.cons_append, List.nil_append]
  wp_fixed_frame [paramsLength]
  apply pushFinish_owned env initial heap _ 72 76 75 74 73 77 78 pointer words value remaining pageLimit
    represented protectedWords valid (by omega) budget
  all_goals first
    | (solve | simp only [Locals.validIndex, Locals.get, paramsLength, List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, need])
    | (solve | decide)
    | skip
  intro final
  dsimp only
  intro finalValid owned frame finalBudget
  simpa only [matrixPushFrame, matrixPrefix, matrixSuffix, FixedArrayCopy.counterFrame, Locals.set, List.set, List.length,
    paramsLength, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte, List.cons_append, List.nil_append, need,
    allocatedNode, Nat.toUInt64] using finish final finalValid owned frame finalBudget previous' current' capacity' next'

#print axioms matrixPushAllocated_owned

end Project.Beck.Execution
