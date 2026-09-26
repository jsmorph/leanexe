import Project.Beck.ExecutionSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def membershipBody : Wasm.Program :=
  match (func2[6]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def membershipInRange : Wasm.Program :=
  match (membershipBody[21]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def membershipFresh : Wasm.Program :=
  match (membershipInRange[24]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def membershipSetBranch : Wasm.Program :=
  match (membershipFresh[35]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def membershipSetAllocated : Wasm.Program :=
  FixedArrayAllocate.program 40 1 ++ [.localGet 45, .localSet 35] ++
    setFinishProgram 31 35 33 34 32 36 37 ++ [.localGet 35]

set_option maxRecDepth 2048 in
theorem membershipSetBranch_shape : membershipSetBranch =
    [.localGet 33, .constI64 1, .mulI64, .localSet 34] ++
      FixedArrayCapacity.localProgram 33 1 40 ++ membershipSetAllocated := rfl

abbrev MemberSetSaved := Fin 24 → Value

def memberSetPrefix (saved : MemberSetSaved) : List Value :=
  [saved 0, saved 1, saved 2, saved 3, saved 4, saved 5, saved 6, saved 7,
    saved 8, saved 9, saved 10, saved 11, saved 12, saved 13, saved 14, saved 15,
    saved 16, saved 17, saved 18, saved 19, saved 20, saved 21, saved 22, saved 23]

def memberSetFrame (params : List Value) (saved : MemberSetSaved) (ptr : UInt64) (index size : Nat)
    (target counter value padding38 padding39 need previous current capacity next result : UInt64)
    (values : List Value := []) : Locals :=
  { params := params
    locals := memberSetPrefix saved ++
      [.i64 ptr, .i64 index.toUInt64, .i64 size.toUInt64, .i64 size.toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding38, .i64 padding39,
        .i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result]
    values := values }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem membershipSetAllocated_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : MemberSetSaved) (paramsLength : params.length = 7)
    (ptr : UInt64) (words : Array UInt64) (index : Nat)
    (target counter value padding38 padding39 previous current capacity next result : UInt64)
    (remaining pageLimit : Nat)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (words.set! index value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (memberSetFrame params saved ptr index words.size node.root words.size.toUInt64 value padding38 padding39
          need previous current capacity next node.root [.i64 node.root]) env) :
    wp Project.Beck.«module» (membershipSetAllocated ++ rest) Q initial
      (memberSetFrame params saved ptr index words.size target counter value padding38 padding39
        (UInt64.ofNat (8 * (words.size + 1))) previous current capacity next result) env := by
  let need := UInt64.ofNat (8 * (words.size + 1))
  have needWord : need.toNat = 8 * (words.size + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  rw [membershipSetAllocated]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 40 1 ++ _) Q initial
    (FixedArraySearch.frame params (memberSetPrefix saved ++
      [.i64 ptr, .i64 index.toUInt64, .i64 words.size.toUInt64, .i64 words.size.toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding38, .i64 padding39]) []
      need previous current capacity next result) env
  apply allocation_exact env initial heap params _ [] 40 (by simp [paramsLength, memberSetPrefix])
    need previous current capacity next result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous' current' capacity' next'
  simp only [FixedArraySearch.frame, memberSetPrefix, List.append_assoc, List.cons_append, List.nil_append]
  wp_fixed_frame [paramsLength]
  apply setFinish_owned env initial heap _ 31 35 33 34 32 36 37 ptr words index value remaining pageLimit
    represented protects valid bound inside budget
  all_goals first
    | (solve | simp only [Locals.validIndex, Locals.get, paramsLength, List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, need])
    | (solve | decide)
    | skip
  intro final
  dsimp only
  intro finalValid owned frame finalBudget
  simp only [FixedArrayCopy.counterFrame, Locals.set, List.set, List.length, paramsLength,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte]
  wp_fixed_frame [paramsLength]
  simpa only [memberSetFrame, memberSetPrefix, List.cons_append, List.nil_append, need, allocatedNode, Nat.toUInt64] using
    finish final finalValid owned frame finalBudget previous' current' capacity' next'

#print axioms membershipSetAllocated_owned

end Project.Beck.Execution
