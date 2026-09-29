import Project.ProofKit.Array
import Project.ProofKit.MemoryFrame
import Project.ProofKit.MemoryRoundtrip

namespace Project.ProofKit.UInt64Array
open Wasm Memory

def PrefixAt (store : Store Unit) (ptr : UInt64) (values : Array UInt64)
    (count : Nat) : Prop :=
  ptr.toNat + 8 * (values.size + 1) ≤ 4294967296 ∧
  ptr.toNat + 8 * (values.size + 1) ≤ store.mem.pages * 65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size ∧
  ∀ (i : Nat) (hi : i < values.size), i < count →
    store.mem.read64 (wordAddress ptr (i + 1)) = values[i]

theorem PrefixAt.empty (store : Store Unit) (ptr : UInt64) (values : Array UInt64)
    (hFit : ptr.toNat + 8 * (values.size + 1) ≤ 4294967296)
    (hMemory : ptr.toNat + 8 * (values.size + 1) ≤ store.mem.pages * 65536)
    (hLength : store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size) :
    PrefixAt store ptr values 0 :=
  ⟨hFit, hMemory, hLength, fun _ _ h => False.elim (by omega)⟩

theorem PrefixAt.complete {store : Store Unit} {ptr : UInt64} {values : Array UInt64}
    (h : PrefixAt store ptr values values.size) : At store ptr values :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi => h.2.2.2 i hi hi⟩

def writeElement (store : Store Unit) (ptr : UInt64) (index : Nat) (value : UInt64) :
    Store Unit :=
  { store with mem := store.mem.write64 (wordAddress ptr (index + 1)) value }

theorem generatedElementAddress (ptr : UInt64) (index : Nat) :
    UInt32.ofNat ((ptr+(UInt64.ofNat index*1+1)*8).toNat % 2^32) = wordAddress ptr (index+1) := by
  have hOffset : (UInt64.ofNat index*1+1)*8 = UInt64.ofNat (8*(index+1)) := by
    rw [UInt64.mul_one]
    change (UInt64.ofNat index+UInt64.ofNat 1)*UInt64.ofNat 8 = _
    rw [← UInt64.ofNat_add, ← UInt64.ofNat_mul, Nat.mul_comm (index+1) 8]
  rw [hOffset]
  exact (Memory.toUInt32_eq_ofNat _).symm

@[simp] theorem writeElement_pages (store : Store Unit) (ptr : UInt64)
    (index : Nat) (value : UInt64) :
    (writeElement store ptr index value).mem.pages = store.mem.pages := Mem.write64_pages ..

theorem PrefixAt.elementBound {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} {count : Nat} (h : PrefixAt store ptr values count)
    (i : Nat) (hi : i < values.size) :
    (wordAddress ptr (i + 1)).toNat + 8 ≤ store.mem.pages * 65536 := by
  rw [wordAddress_toNat h.1 (by omega)]
  have := h.2.1
  omega

theorem PrefixAt.write_next {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} {index : Nat} (h : PrefixAt store ptr values index)
    (hi : index < values.size) :
    PrefixAt (writeElement store ptr index values[index]) ptr values (index + 1) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · simpa only [writeElement_pages] using h.2.1
  · apply (read64_write64_disjoint store.mem _ _ ptr.toUInt32 ?_).trans h.2.2.1
    left
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by have := h.1; omega),
      wordAddress_toNat h.1 (by omega)]
    omega
  · intro j hj hPrefix
    by_cases heq : j = index
    · subst j
      exact read64_write64 ..
    · apply (read64_write64_disjoint store.mem _ _ _ ?_).trans (h.2.2.2 j hj (by omega))
      rw [wordAddress_toNat h.1 (by omega), wordAddress_toNat h.1 (by omega)]
      omega

theorem writeElement_frame (store : Store Unit) (ptr : UInt64) (size index : Nat)
    (value : UInt64) (hFit : ptr.toNat + 8 * (size + 1) ≤ 4294967296)
    (hi : index < size) :
    WritesRange store (writeElement store ptr index value)
      ptr.toNat (ptr.toNat + 8 * (size + 1)) := by
  apply WritesRange.write64
  · rw [wordAddress_toNat hFit (by omega)]
    omega
  · rw [wordAddress_toNat hFit (by omega)]
    omega

theorem At.frame {initial final : Store Unit} {ptr : UInt64} {values : Array UInt64}
    (h : At initial ptr values) (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address : Nat,
      ptr.toNat ≤ address → address < ptr.toNat + 8 * (values.size + 1) →
      final.mem.bytes address = initial.mem.bytes address) : At final ptr values := by
  refine ⟨h.1, h.2.1.trans (Nat.mul_le_mul_right 65536 hPages), ?_, ?_⟩
  · apply (read64_congr ptr.toUInt32 ?_).trans h.lengthRead
    intro byte hByte
    apply hBytes <;> rw [h.pointerAddress_toNat] <;> omega
  · intro i hi
    apply (read64_congr _ ?_).trans (h.elementRead i hi)
    intro byte hByte
    apply hBytes <;> rw [h.elementAddress_toNat i hi] <;> omega

theorem At.writesRange {initial final : Store Unit} {ptr : UInt64}
    {values : Array UInt64} {start stop : Nat} (h : At initial ptr values)
    (hWrites : WritesRange initial final start stop)
    (hDisjoint : ptr.toNat + 8 * (values.size + 1) ≤ start ∨ stop ≤ ptr.toNat) :
    At final ptr values :=
  h.frame hWrites.2.1.ge (fun _ hLow hHigh => hWrites.2.2 _ (by omega))

#print axioms PrefixAt.empty
#print axioms PrefixAt.complete
#print axioms PrefixAt.elementBound
#print axioms PrefixAt.write_next
#print axioms writeElement_frame
#print axioms At.frame
#print axioms At.writesRange

end Project.ProofKit.UInt64Array
