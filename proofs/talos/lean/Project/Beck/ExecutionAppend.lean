import Project.Beck.ExecutionBudget
import Project.ProofKit.ArrayAppend

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def appendFinishProgram (leftLocal rightLocal targetLocal lengthLocal leftCountLocal rightCountLocal counterLocal : Nat) : Wasm.Program :=
  FixedArrayResult.lengthStoreLocalProgram targetLocal lengthLocal ++
    FixedArrayCopy.prefixProgram leftLocal targetLocal leftCountLocal counterLocal ++
      OffsetArrayCopy.program rightLocal targetLocal rightCountLocal counterLocal none (some leftCountLocal)

theorem appendFinish_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (frame : Locals)
    (leftLocal rightLocal targetLocal lengthLocal leftCountLocal rightCountLocal counterLocal : Nat)
    (leftPointer rightPointer : UInt64) (left right : Array UInt64) (remaining pageLimit : Nat)
    (leftAt : UInt64Array.At initial leftPointer left) (rightAt : UInt64Array.At initial rightPointer right)
    (leftProtected : heap.Protects leftPointer.toNat (leftPointer.toNat + 8 * (left.size + 1)))
    (rightProtected : heap.Protects rightPointer.toNat (rightPointer.toNat + 8 * (right.size + 1)))
    (valid : heap.At initial) (bound : left.size + right.size ≤ 56)
    (budget : OutputBudget initial heap (48 + 8 * (left.size + right.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (counterValid : frame.validIndex counterLocal) (values : frame.values = [])
    (leftDifferent : leftLocal ≠ counterLocal) (rightDifferent : rightLocal ≠ counterLocal)
    (targetDifferent : targetLocal ≠ counterLocal) (leftCountDifferent : leftCountLocal ≠ counterLocal)
    (rightCountDifferent : rightCountLocal ≠ counterLocal)
    (leftRead : frame.get leftLocal = some (.i64 leftPointer)) (rightRead : frame.get rightLocal = some (.i64 rightPointer))
    (targetRead : frame.get targetLocal = some (.i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (left.size + right.size + 1))) heap.nodes)))
    (lengthRead : frame.get lengthLocal = some (.i64 (left.size + right.size).toUInt64))
    (leftCountRead : frame.get leftCountLocal = some (.i64 left.size.toUInt64))
    (rightCountRead : frame.get rightCountLocal = some (.i64 right.size.toUInt64))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final,
      let need := UInt64.ofNat (8 * (left.size + right.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (left ++ right) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final (FixedArrayCopy.counterFrame frame counterLocal right.size counterValid) env) :
    wp Project.Beck.«module»
      (appendFinishProgram leftLocal rightLocal targetLocal lengthLocal leftCountLocal rightCountLocal counterLocal ++ rest) Q
      (heap.allocateArrayStore initial (UInt64.ofNat (8 * (left.size + right.size + 1))) 1) frame env := by
  let size := left.size + right.size
  let need := UInt64.ofNat (8 * (size + 1))
  let root := allocatedRoot heap.top need heap.nodes
  let allocated := heap.allocateArrayStore initial need 1
  let header := FixedArrayResult.writeLength allocated root size.toUInt64
  have needWord : need.toNat = 8 * (size + 1) := by dsimp [need, size]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  have bump : takeFirstFitFrom 0 need heap.nodes = none → heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => (space h).1.le
  have bounds := allocated_bounds initial heap.top need heap.nodes valid.freeList bump
  have capacity := allocated_capacity need heap.nodes
  rw [needWord] at capacity
  have targetBound : root.toNat + 8 * (size + 1) ≤ 4294967296 := by dsimp [root]; omega
  have targetMemory : root.toNat + 8 * (size + 1) ≤ allocated.mem.pages * 65536 := by
    change root.toNat + 8 * (size + 1) ≤ (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    dsimp [root]
    omega
  have rootNat : root.toUInt32.toNat = root.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have headerWrites : Memory.WritesRange allocated header root.toNat (root.toNat + 8 * (size + 1)) := by
    apply Memory.WritesRange.write64 <;> rw [rootNat] <;> omega
  have allocatedFrame := heap.frame_allocate initial need 1 valid bump
  have leftSeparate := leftProtected.allocated_disjoint need bump
  have rightSeparate := rightProtected.allocated_disjoint need bump
  have leftHeader := (allocatedFrame.words leftProtected leftAt).writesRange headerWrites (by dsimp [root]; omega)
  have rightHeader := (allocatedFrame.words rightProtected rightAt).writesRange headerWrites (by dsimp [root]; omega)
  rw [appendFinishProgram, List.append_assoc, List.append_assoc]
  apply FixedArrayResult.lengthStoreLocal_spec Project.Beck.«module» env allocated frame root size.toUInt64 targetLocal lengthLocal
    targetRead lengthRead (by rw [rootNat]; omega)
  apply UInt64Array.appendCopy_spec leftLocal rightLocal targetLocal leftCountLocal rightCountLocal counterLocal
    Project.Beck.«module» env header frame leftPointer rightPointer root left right counterValid values leftDifferent
    rightDifferent targetDifferent leftCountDifferent rightCountDifferent leftRead rightRead targetRead leftCountRead rightCountRead
    leftHeader rightHeader targetBound (by simpa only [header, FixedArrayResult.writeLength, Mem.write64_pages] using targetMemory)
    (Memory.read64_write64 ..) (by dsimp [root]; omega) (by dsimp [root]; omega)
  intro final writes _ _ output
  have total := headerWrites.trans writes
  have outputWrites : Memory.WritesRange allocated final root.toNat (root.toNat + 8 * ((left ++ right).size + 1)) := by
    simpa only [Array.size_append] using total
  obtain ⟨finalValid, owned⟩ := heap.finishWords initial final need (left ++ right) valid
    (by rw [Array.size_append, needWord]) (fun h => (space h).1) outputWrites output
  exact next final finalValid owned (heap.frame_arrayWritten initial final need 1 size valid (by rw [needWord]) bump total)
    (budget.allocated need 1 remaining (by rw [needWord]) total)

#print axioms appendFinish_owned

end Project.Beck.Execution
