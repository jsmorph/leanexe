import Project.ClobMatchFuel.ReleaseFrame

/-!
# Memory frames above a reserved heap boundary

The matching proof reserves enough memory below one natural-number boundary for
every remaining allocation.  These lemmas compose allocator, payload, and
release writes while preserving every byte at or above that boundary.
-/

namespace Project.ClobMatchFuel.MemoryFrame

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

def BytesEqFrom (before after : Mem) (limit : Nat) : Prop :=
  ∀ a : Nat, limit ≤ a → after.bytes a = before.bytes a

theorem BytesEqFrom.refl (mem : Mem) (limit : Nat) :
    BytesEqFrom mem mem limit := by
  intro _ _
  rfl

theorem BytesEqFrom.trans {first middle last : Mem} {limit : Nat}
    (hFirst : BytesEqFrom first middle limit)
    (hLast : BytesEqFrom middle last limit) :
    BytesEqFrom first last limit := by
  intro a ha
  rw [hLast a ha, hFirst a ha]

theorem BytesEqFrom.of_outsideFlatWords
    {before after : Store Unit} {ptr : UInt64} {words limit : Nat}
    (hEnd : ptr.toNat + (words + 1) * 8 ≤ limit)
    (hOutside : MemEqOutsideFlatWords before after ptr words) :
    BytesEqFrom before.mem after.mem limit := by
  intro a ha
  exact hOutside a (Or.inr (hEnd.trans ha))

theorem fixedArrayAllocFitStore_bytesFrom
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {stride : UInt64} {limit : Nat}
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ limit) :
    BytesEqFrom st.mem
      (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem limit := by
  intro a ha
  have frameWrite (current : Mem) (writer : FreeNode)
      (hWriter : writer ∈ nodes) (offset value : UInt64)
      (hOffsetLow : 8 ≤ offset.toNat)
      (hOffsetHigh : offset.toNat ≤ 48) :
      (current.write64 ((writer.root - offset).toUInt32) value).bytes a =
        current.bytes a := by
    obtain ⟨hWriter48, hWriter32, _⟩ := hList.mem_bounds hWriter
    apply write64_bytes_ne
    right
    rw [toUInt32_toNat,
      toNat_sub_le writer.root offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
    have hWriterBelow := hBelow writer hWriter
    omega
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  have hUnlink : (unlinkFreeChoice st.mem choice).bytes a = st.mem.bytes a := by
    by_cases hPrevious : choice.previous = 0
    · simp [unlinkFreeChoice, hPrevious]
    · obtain ⟨skipped, tail, hNodes, hPreviousRoot, _, _, _⟩ :=
        takeFirstFitFrom_some_decompose hTake
      have hSkipped : skipped ≠ [] := by
        intro hEmpty
        subst skipped
        simp only [previousRoot] at hPreviousRoot
        exact hPrevious hPreviousRoot
      let predecessor := skipped.getLast hSkipped
      have hSplit : skipped.dropLast ++ [predecessor] = skipped :=
        List.dropLast_append_getLast hSkipped
      have hPreviousEq : choice.previous = predecessor.root := by
        rw [hPreviousRoot, ← hSplit, previousRoot_append_singleton]
      have hPredecessorMem : predecessor ∈ nodes := by
        rw [hNodes, ← hSplit]
        simp
      rw [unlinkFreeChoice, if_neg hPrevious, hPreviousEq]
      exact frameWrite st.mem predecessor hPredecessorMem 8 choice.next
        (by decide) (by decide)
  unfold BookAllocFit.fixedArrayAllocFitStore
  change (BookAllocFit.fixedArrayAllocFitMem st.mem choice stride).bytes a =
    st.mem.bytes a
  unfold BookAllocFit.fixedArrayAllocFitMem
  rw [frameWrite _ choice.node hChoiceMem 8 0 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 16 stride (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 24 2 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 32 choice.node.capacity
      (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 40 1 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 48 5501223100278326855
      (by decide) (by decide),
    hUnlink]

theorem fixedArrayAllocBumpStore_bytesFrom
    (st : Store Unit) (g0 need stride : UInt64) (limit : Nat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hEnd : g0.toNat + 48 + need.toNat ≤ limit) :
    BytesEqFrom st.mem
      (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem limit := by
  intro a ha
  change (fixedArrayHeaderMem st.mem g0 need stride).bytes a = st.mem.bytes a
  unfold fixedArrayHeaderMem
  rw [write64_bytes_ne _ _ _ (by
        right
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega),
    write64_bytes_ne _ _ _ (by
        right
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega),
    write64_bytes_ne _ _ _ (by
        right
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega),
    write64_bytes_ne _ _ _ (by
        right
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega),
    write64_bytes_ne _ _ _ (by
        right
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega),
    write64_bytes_ne _ _ _ (by
        right
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega)]

theorem fixedArrayReleaseMem_bytesFrom
    (st : Store Unit) (ptr capacity freeHead : UInt64) (limit : Nat)
    (hPtr48 : 48 ≤ ptr.toNat)
    (hPtr32 : ptr.toNat + capacity.toNat < 4294967296)
    (hEnd : ptr.toNat + capacity.toNat ≤ limit) :
    BytesEqFrom st.mem (fixedArrayReleaseMem st ptr freeHead) limit := by
  intro a ha
  have hOutside (offset : UInt64) (hOffsetLow : 8 ≤ offset.toNat)
      (hOffsetHigh : offset.toNat ≤ 40) :
      a < ((ptr - offset).toUInt32).toNat ∨
        ((ptr - offset).toUInt32).toNat + 8 ≤ a := by
    right
    rw [toUInt32_toNat, toNat_sub_le ptr offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  unfold fixedArrayReleaseMem
  rw [write64_bytes_ne _ _ _ (hOutside 8 (by decide) (by decide)),
    write64_bytes_ne _ _ _ (hOutside 40 (by decide) (by decide))]

end Project.ClobMatchFuel.MemoryFrame
