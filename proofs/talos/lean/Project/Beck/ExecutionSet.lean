import Project.Beck.ExecutionBudget
import Project.ProofKit.ArraySet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def setFinishProgram (sourceLocal targetLocal lengthLocal countLocal indexLocal counterLocal valueLocal : Nat) : Wasm.Program :=
  FixedArrayResult.lengthStoreLocalProgram targetLocal lengthLocal ++
    FixedArrayCopy.prefixProgram sourceLocal targetLocal countLocal counterLocal ++
      UInt64Array.setStoreProgram targetLocal indexLocal valueLocal

theorem setFinish_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (frame : Locals)
    (sourceLocal targetLocal lengthLocal countLocal indexLocal counterLocal valueLocal : Nat)
    (ptr : UInt64) (words : Array UInt64) (index : Nat) (value : UInt64) (remaining pageLimit : Nat)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hSourceNe : sourceLocal ≠ counterLocal) (hTargetNe : targetLocal ≠ counterLocal)
    (hCountNe : countLocal ≠ counterLocal) (hIndexNe : indexLocal ≠ counterLocal) (hValueNe : valueLocal ≠ counterLocal)
    (hSource : frame.get sourceLocal = some (.i64 ptr))
    (hTarget : frame.get targetLocal = some (.i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (words.size + 1))) heap.nodes)))
    (hLength : frame.get lengthLocal = some (.i64 words.size.toUInt64))
    (hCount : frame.get countLocal = some (.i64 words.size.toUInt64))
    (hIndex : frame.get indexLocal = some (.i64 index.toUInt64)) (hValue : frame.get valueLocal = some (.i64 value))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final,
      let need := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (words.set! index value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final (FixedArrayCopy.counterFrame frame counterLocal words.size hCounter) env) :
    wp Project.Beck.«module»
      (setFinishProgram sourceLocal targetLocal lengthLocal countLocal indexLocal counterLocal valueLocal ++ rest) Q
      (heap.allocateArrayStore initial (UInt64.ofNat (8 * (words.size + 1))) 1) frame env := by
  let need := UInt64.ofNat (8 * (words.size + 1))
  let root := allocatedRoot heap.top need heap.nodes
  let allocated := heap.allocateArrayStore initial need 1
  let header := FixedArrayResult.writeLength allocated root words.size.toUInt64
  have needWord : need.toNat = 8 * (words.size + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  have bump : takeFirstFitFrom 0 need heap.nodes = none → heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => (space h).1.le
  have bounds := allocated_bounds initial heap.top need heap.nodes valid.freeList bump
  have needCapacity := allocated_capacity need heap.nodes
  rw [needWord] at needCapacity
  have targetBound : root.toNat + 8 * (words.size + 1) ≤ 4294967296 := by dsimp [root]; omega
  have targetMemory : root.toNat + 8 * (words.size + 1) ≤ allocated.mem.pages * 65536 := by
    change root.toNat + 8 * (words.size + 1) ≤ (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    dsimp [root]
    omega
  have rootForm : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have headerWrites : Project.ProofKit.Memory.WritesRange allocated header root.toNat (root.toNat + 8) := by
    apply Project.ProofKit.Memory.WritesRange.write64 <;> rw [rootForm]
  have allocationFrame := heap.frame_allocate initial need 1 valid bump
  have sourceAllocated := allocationFrame.words protects represented
  have separated := protects.allocated_disjoint need bump
  have sourceHeader : UInt64Array.At header ptr words := by
    apply sourceAllocated.writesRange headerWrites
    dsimp [root]
    omega
  rw [setFinishProgram, List.append_assoc, List.append_assoc]
  refine FixedArrayResult.lengthStoreLocal_spec Project.Beck.«module» env allocated frame root words.size.toUInt64
    targetLocal lengthLocal hTarget hLength (by rw [rootForm]; omega) _ _ ?_
  apply UInt64Array.setCopy_spec sourceLocal targetLocal countLocal indexLocal counterLocal valueLocal
    Project.Beck.«module» env header frame ptr root words index value hCounter hValues hSourceNe hTargetNe hCountNe hIndexNe
    hValueNe hSource hTarget hCount hIndex hValue sourceHeader inside targetBound
    (by simpa only [header, FixedArrayResult.writeLength, Mem.write64_pages] using targetMemory)
    (Project.ProofKit.Memory.read64_write64 ..) (by dsimp [root]; omega)
  intro final writes _ output
  have total := (headerWrites.mono (Nat.le_refl _) (by omega)).trans writes
  have outputSize : (words.set! index value).size = words.size := by simp
  have outputWrites : Project.ProofKit.Memory.WritesRange allocated final root.toNat
      (root.toNat + 8 * ((words.set! index value).size + 1)) := by simpa only [outputSize] using total
  obtain ⟨finalValid, owned⟩ := heap.finishWords initial final need (words.set! index value) valid
    (by rw [outputSize, needWord]) (fun h => (space h).1) outputWrites output
  have preserved := heap.frame_arrayWritten initial final need 1 words.size valid (by rw [needWord]) bump total
  exact next final finalValid owned preserved (budget.allocated need 1 remaining (by rw [needWord]) total)

#print axioms setFinish_owned

end Project.Beck.Execution
