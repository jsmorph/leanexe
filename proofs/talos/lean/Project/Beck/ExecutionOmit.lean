import Project.Beck.ExecutionHeap
import Project.ProofKit.FixedArrayErase

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def omitPrelude : Wasm.Program :=
  [.localGet 10, .constI64 1, .subI64, .localSet 13,
    .localGet 9, .constI64 1, .mulI64, .localSet 11,
    .localGet 13, .localGet 9, .subI64, .constI64 1, .mulI64, .localSet 12]

def omitCopy : Wasm.Program :=
  [.localGet 23, .localSet 14] ++ FixedArrayResult.lengthStoreLocalProgram 14 13 ++
    FixedArrayCopy.program 1 8 14 11 12 15 ++ [.localGet 14]

def omitBranch : Wasm.Program :=
  omitPrelude ++ FixedArrayCapacity.localProgram 13 1 18 ++
    FixedArrayAllocate.program 18 1 ++ omitCopy

theorem omit_program : func23 = func23.take 15 ++
    [.iff 0 1 omitBranch [.localGet 8] [] [.i64]] ++ func23.drop 16 := by rfl

theorem words_capacity (size : Nat) (bound : size ≤ 56) :
    FixedArrayCapacity.normalizedCapacity (UInt64.ofNat size) 1 = UInt64.ofNat (8 * (size + 1)) := by
  have raw : (FixedArrayCapacity.unnormalizedCapacity (UInt64.ofNat size) 1).toNat = 8 * (size + 1) := by
    simp only [FixedArrayCapacity.unnormalizedCapacity, UInt64.mul_one,
      UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
    norm_num
    omega
  have small : ¬FixedArrayCapacity.unnormalizedCapacity (UInt64.ofNat size) 1 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, raw]
    change ¬8 * (size + 1) < 8
    omega
  simp only [FixedArrayCapacity.normalizedCapacity, ite_eq_right small]
  apply UInt64.toNat_inj.mp
  rw [raw, UInt64.toNat_ofNat']
  omega

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem omitIndex_inBounds (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (words : Array UInt64) (ptr owner : UInt64) (index : Nat)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (space : takeFirstFitFrom 0 (UInt64.ofNat (8 * words.size)) heap.nodes = none →
      heap.top.toNat + 48 + 8 * words.size < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (UInt64.ofNat (8 * words.size)) ≤
        initial.memoryCap Project.Beck.«module» 0)
    (pages : initial.mem.pages ≤ 65536) :
    TerminatesWith env Project.Beck.«module» 23 initial [.i64 index.toUInt64, .i64 ptr, .i64 owner]
      (fun final values =>
        let need := UInt64.ofNat (8 * words.size)
        let node := allocatedNode heap.top need heap.nodes
        values = [.i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).OwnsWords final node (omitIndex words index) ∧
        heap.Frame initial (heap.allocate need) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.Beck.«module» 0 = initial.memoryCap Project.Beck.«module» 0 ∧
        Project.ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
          node.root.toNat (node.root.toNat + 8 * words.size)) := by
  have indexWord : (UInt64.ofNat index).toNat = index := by rw [UInt64.toNat_ofNat']; omega
  have sizeWord : (UInt64.ofNat words.size).toNat = words.size := by rw [UInt64.toNat_ofNat']; omega
  have needWord : (UInt64.ofNat (8 * words.size)).toNat = 8 * words.size := by
    rw [UInt64.toNat_ofNat']; omega
  have ltWord : UInt64.ofNat index < UInt64.ofNat words.size := by
    rw [UInt64.lt_iff_toNat_lt, indexWord, sizeWord]; exact inside
  have subOne : UInt64.ofNat words.size - 1 = UInt64.ofNat (words.size - 1) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
    norm_num
    omega
  have subIndex : UInt64.ofNat (words.size - 1) - UInt64.ofNat index =
      UInt64.ofNat (words.size - 1 - index) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat']
    norm_num
    omega
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_
  change wp Project.Beck.«module» func23 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 index.toUInt64], locals := List.replicate 21 (.i64 0) } env
  rw [omit_program]
  simp only [func23, List.take, List.drop, List.cons_append, List.nil_append]
  wp_fixed_frame [represented.lengthRead, represented.pointerAddress_toNat, represented.2.1]
  have ptrForm : UInt32.ofNat (ptr.toNat % 2^32) = ptr.toUInt32 :=
    (Project.ProofKit.Memory.toUInt32_eq_ofNat ptr).symm
  have headerFits : ptr.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [represented.pointerAddress_toNat]
    have := represented.2.1
    omega
  simp only [ptrForm, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
    show ¬ptr.toUInt32.toNat + 8 > initial.mem.pages * 65536 from by omega,
    ite_false, represented.lengthRead]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left ltWord, ite_eq_left (by decide)]
  simp only [omitBranch, omitPrelude, List.append_assoc, List.cons_append, List.nil_append]
  wp_fixed_frame [subOne, subIndex]
  apply FixedArrayCapacity.localProgram_spec 13 (UInt64.ofNat (words.size - 1)) 1 18
    Project.Beck.«module» env initial _ rfl rfl (by simp) (by simp [Locals.validIndex])
  have capacityEq := words_capacity (words.size - 1) (by omega)
  have resultSize : words.size - 1 + 1 = words.size := by omega
  rw [resultSize] at capacityEq
  rw [capacityEq]
  simp only [UInt64.mul_one]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 18 1 ++ _) _ initial
    (FixedArraySearch.frame [.i64 owner, .i64 ptr, .i64 index.toUInt64]
      [.i64 ptr, .i64 index.toUInt64, .i64 0, .i64 0, .i64 0, .i64 ptr, .i64 index.toUInt64,
        .i64 words.size.toUInt64, .i64 index.toUInt64, .i64 (words.size - 1 - index).toUInt64,
        .i64 (words.size - 1).toUInt64, .i64 0, .i64 0, .i64 0, .i64 0]
      [] (UInt64.ofNat (8 * words.size)) 0 0 0 0 0) env
  apply allocation_exact env initial heap _ _ [] 18 rfl _ 0 0 0 0 0 valid
    (fun h => ⟨by rw [needWord]; exact (space h).1.le, (space h).2⟩) pages
  intro previous current capacity next
  let need := UInt64.ofNat (8 * words.size)
  let root := allocatedRoot heap.top need heap.nodes
  let allocated := heap.allocateArrayStore initial need 1
  let header := FixedArrayResult.writeLength allocated root (UInt64.ofNat (words.size - 1))
  have bump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro h
    change heap.top.toNat + 48 + (UInt64.ofNat (8 * words.size)).toNat ≤ _
    rw [needWord]
    exact (space h).1.le
  have bounds := allocated_bounds initial heap.top need heap.nodes valid.freeList bump
  have needCapacity := allocated_capacity need heap.nodes
  change (UInt64.ofNat (8 * words.size)).toNat ≤ (allocatedCapacity need heap.nodes).toNat at needCapacity
  rw [needWord] at needCapacity
  have targetBound : root.toNat + 8 * words.size ≤ 4294967296 := by
    dsimp [root]
    omega
  have targetMemory : root.toNat + 8 * words.size ≤ allocated.mem.pages * 65536 := by
    change root.toNat + 8 * words.size ≤
      (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
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
  simp only [omitCopy, List.append_assoc, List.cons_append, List.nil_append, FixedArraySearch.frame]
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine FixedArrayResult.lengthStoreLocal_spec Project.Beck.«module» env allocated _
    root (UInt64.ofNat (words.size - 1)) 14 13 rfl rfl
    (by rw [rootForm]; omega) _ _ ?_
  refine FixedArrayCopy.eraseIdxProgram_framed_spec 8 14 11 12 15
    Project.Beck.«module» env header _ ptr root words index inside sourceHeader
    (by simp [Locals.validIndex]) (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl (by simpa only [resultSize] using targetBound)
    (by simpa only [resultSize, header, FixedArrayResult.writeLength, Mem.write64_pages] using targetMemory)
    (Project.ProofKit.Memory.read64_write64 ..) (by dsimp [root]; omega) _ _ ?_
  intro final output copyWrites
  have writes : Project.ProofKit.Memory.WritesRange allocated final root.toNat
      (root.toNat + 8 * words.size) :=
    (headerWrites.mono (Nat.le_refl _) (by omega)).trans (copyWrites.mono (by omega) (Nat.le_refl _))
  have outputEq : words.eraseIdx! index = omitIndex words index := by
    simp [Array.eraseIdx!, omitIndex, inside, ← Array.eraseIdx_eq_eraseIdxIfInBounds inside]
  have outputSize : (omitIndex words index).size + 1 = words.size := by
    simp only [omitIndex, ← Array.eraseIdx_eq_eraseIdxIfInBounds inside, Array.size_eraseIdx]
    omega
  rw [outputEq] at output
  have writesOutput : Project.ProofKit.Memory.WritesRange allocated final root.toNat
      (root.toNat + 8 * ((omitIndex words index).size + 1)) := by
    simpa only [outputSize] using writes
  obtain ⟨finalHeap, owned⟩ := heap.finishWords initial final need (omitIndex words index) valid
    (by rw [outputSize]; exact needWord.ge) (fun h => by simpa only [need, needWord] using (space h).1)
    writesOutput output
  have frame := heap.frame_arrayWritten initial final need 1 (words.size - 1) valid
    (by rw [resultSize]; exact needWord.ge) bump (by simpa only [resultSize] using writes)
  have sourceFinal := frame.words protects represented
  have finalHeaderFits : ptr.toUInt32.toNat + 8 ≤ final.mem.pages * 65536 := by
    rw [represented.pointerAddress_toNat]
    have := sourceFinal.2.1
    omega
  simp only [FixedArrayCopy.counterFrame, Locals.set, List.set, List.length,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte]
  wp_fixed_frame [List.take, List.append_nil, ptrForm, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, sourceFinal.lengthRead,
    show ¬ptr.toUInt32.toNat + 8 > final.mem.pages * 65536 from by omega]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left ltWord, ite_eq_left (by decide)]
  wp_fixed_frame [List.take, List.append_nil, func23Def]
  obtain ⟨finalPages, finalCap⟩ := allocatedWrites_resources heap initial final need _ _ writes bump pages
  exact ⟨rfl, finalHeap, owned, frame, finalPages, finalCap, writes⟩

theorem omitIndex_outOfBounds (env : HostEnv Unit) (initial : Store Unit)
    (words : Array UInt64) (ptr owner index : UInt64)
    (represented : UInt64Array.At initial ptr words) (outside : words.size ≤ index.toNat) :
    TerminatesWith env Project.Beck.«module» 23 initial [.i64 index, .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 ptr, .i64 owner]) := by
  have sizeFit : words.size < UInt64.size := by
    change words.size < 18446744073709551616
    have := represented.1
    omega
  have ltWord : ¬index < UInt64.ofNat words.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' sizeFit]
    omega
  have ptrForm : UInt32.ofNat (ptr.toNat % 2^32) = ptr.toUInt32 :=
    (Project.ProofKit.Memory.toUInt32_eq_ofNat ptr).symm
  have headerFits : ¬ptr.toUInt32.toNat + 8 > initial.mem.pages * 65536 := by
    rw [represented.pointerAddress_toNat]
    have := represented.2.1
    omega
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_
  change wp Project.Beck.«module» func23 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 index], locals := List.replicate 21 (.i64 0) } env
  rw [omit_program]
  simp only [func23, List.take, List.drop, List.cons_append, List.nil_append]
  wp_fixed_frame [ptrForm, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
    headerFits, represented.lengthRead]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right ltWord, ite_eq_right (by decide)]
  wp_fixed_frame [List.take, List.append_nil, ptrForm, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, headerFits, represented.lengthRead]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right ltWord, ite_eq_right (by decide)]
  wp_fixed_frame [List.take, List.append_nil, func23Def]
  simp

#print axioms omitIndex_inBounds
#print axioms omitIndex_outOfBounds

end Project.Beck.Execution
