import Project.Beck.ExecutionSet
import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def wordSetFrame (params saved tail : List Value) (ptr : UInt64) (index length : Nat)
    (target counter value padding1 padding2 need previous current capacity afterNode result : UInt64)
    (values : List Value := []) : Locals :=
  { (FixedArraySearch.frame params (saved ++
      [.i64 ptr, .i64 index.toUInt64, .i64 length.toUInt64, .i64 length.toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding1, .i64 padding2]) tail
      need previous current capacity afterNode result) with values := values }

def wordSetProgram (start : Nat) : Wasm.Program :=
  FixedArrayCapacity.localProgram (start + 2) 1 (start + 9) ++
    FixedArrayAllocate.program (start + 9) 1 ++ [.localGet (start + 14), .localSet (start + 4)] ++
      setFinishProgram start (start + 4) (start + 2) (start + 3) (start + 1) (start + 5) (start + 6) ++ [.localGet (start + 4)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem wordSet_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (start : Nat) (atStart : params.length + saved.length = start)
    (ptr : UInt64) (words : Array UInt64) (index : Nat)
    (target counter value padding1 padding2 need previous current capacity afterNode result : UInt64)
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.set! index value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      wp Project.Beck.«module» rest Q final
        (wordSetFrame params saved tail ptr index words.size node.root words.size.toUInt64 value padding1 padding2
          size previous current capacity afterNode node.root [.i64 node.root]) env) :
    wp Project.Beck.«module» (wordSetProgram start ++ rest) Q initial
      (wordSetFrame params saved tail ptr index words.size target counter value padding1 padding2
        need previous current capacity afterNode result) env := by
  subst start
  let size := UInt64.ofNat (8 * (words.size + 1))
  have sizeWord : size.toNat = 8 * (words.size + 1) := by dsimp [size]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump size (by rw [sizeWord]; omega)
  have fresh := allocated_fresh heap heap initial initial (Heap.Frame.refl heap initial) size (fun h => (space h).1.le)
  simp only [wordSetProgram, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec (params.length + saved.length + 2) words.size.toUInt64 1 (params.length + saved.length + 9)
    Project.Beck.«module» env initial _
    (by simp [wordSetFrame, Locals.get, FixedArraySearch.frame, Nat.add_assoc]) rfl
    (by simp [wordSetFrame, FixedArraySearch.frame]; omega)
    (by simp [wordSetFrame, Locals.validIndex, FixedArraySearch.frame]; omega)
  rw [words_capacity words.size bound]
  have capacityFrame : FixedArrayCapacity.capacityFrame
      (wordSetFrame params saved tail ptr index words.size target counter value padding1 padding2 need previous current capacity afterNode result)
      (params.length + saved.length + 9) size =
      wordSetFrame params saved tail ptr index words.size target counter value padding1 padding2 size previous current capacity afterNode result := by
    simp [FixedArrayCapacity.capacityFrame, wordSetFrame, FixedArraySearch.frame, Nat.add_assoc]
  rw [capacityFrame]
  apply allocation_exact env initial heap params _ tail (params.length + saved.length + 9) (by simp [Nat.add_assoc])
    size previous current capacity afterNode result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity afterNode
  simp only [List.cons_append, List.nil_append]
  simp (discharger := omega) [wp_localGet_cons, wp_localSet_cons, Locals.get, Locals.set?,
    FixedArraySearch.frame, List.length_append, List.length_cons, List.getElem?_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.add_assoc, Nat.reduceAdd, reduceIte]
  simp only [← Nat.add_assoc]
  apply setFinish_owned env initial heap _ (params.length + saved.length) (params.length + saved.length + 4)
    (params.length + saved.length + 2) (params.length + saved.length + 3) (params.length + saved.length + 1)
    (params.length + saved.length + 5) (params.length + saved.length + 6) ptr words index value remaining pageLimit
    represented protects valid bound inside budget
  all_goals first
    | (solve | simp (discharger := omega) [Locals.validIndex, Locals.get, List.getElem?_append,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_assoc, size])
    | (solve | omega)
    | (solve | rfl)
    | skip
  intro final
  dsimp only
  intro finalValid owned preserved finalBudget
  simp (discharger := omega) [FixedArrayCopy.counterFrame, Locals.set, wp_localGet_cons, Locals.get, Nat.add_assoc]
  simpa [wordSetFrame, FixedArraySearch.frame, Nat.add_assoc, allocatedNode, size] using
    finish final finalValid owned preserved fresh finalBudget previous current capacity afterNode

#print axioms wordSet_exact

end Project.Beck.Execution
