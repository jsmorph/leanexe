import Project.ProofKit.FixedWidthArray

namespace Project.ProofKit.FixedWidthArray
open Wasm Memory UInt64Array

def PrefixAt (stride : Nat) (field : α → Nat → UInt64)
    (store : Store Unit) (ptr : UInt64) (values : Array α) (count : Nat) : Prop :=
  ptr.toNat + 8*(stride*values.size+1) ≤ 4294967296 ∧
  ptr.toNat + 8*(stride*values.size+1) ≤ store.mem.pages*65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size ∧
  ∀ (i : Nat) (hi : i < values.size) (f : Nat), f < stride → stride*i+f < count →
    store.mem.read64 (wordAddress ptr (stride*i+f+1)) = field values[i] f

theorem PrefixAt.empty (stride : Nat) (field : α → Nat → UInt64)
    (store : Store Unit) (ptr : UInt64) (values : Array α)
    (hFit : ptr.toNat + 8*(stride*values.size+1) ≤ 4294967296)
    (hMemory : ptr.toNat + 8*(stride*values.size+1) ≤ store.mem.pages*65536)
    (hLength : store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size) :
    PrefixAt stride field store ptr values 0 :=
  ⟨hFit, hMemory, hLength, fun _ _ _ _ h => False.elim (by omega)⟩

theorem PrefixAt.complete {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : PrefixAt stride field store ptr values (stride*values.size)) :
    At stride field store ptr values :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi f hf => h.2.2.2 i hi f hf (field_index_lt hi hf)⟩

def writeField (stride : Nat) (store : Store Unit) (ptr : UInt64) (i f : Nat)
    (value : UInt64) : Store Unit :=
  { store with mem := store.mem.write64 (wordAddress ptr (stride*i+f+1)) value }

@[simp] theorem writeField_pages (stride : Nat) (store : Store Unit) (ptr : UInt64)
    (i f : Nat) (value : UInt64) :
    (writeField stride store ptr i f value).mem.pages = store.mem.pages := Mem.write64_pages ..

theorem PrefixAt.fieldBound {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} {count : Nat}
    (h : PrefixAt stride field store ptr values count) (i f : Nat)
    (hi : i < values.size) (hf : f < stride) :
    (wordAddress ptr (stride*i+f+1)).toNat + 8 ≤ store.mem.pages*65536 := by
  rw [fieldAddress_toNat h.1 hi hf]
  have := field_index_lt hi hf
  have := h.2.1
  omega

theorem PrefixAt.write_next {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} {i f : Nat}
    (h : PrefixAt stride field store ptr values (stride*i+f))
    (hi : i < values.size) (hf : f < stride) :
    PrefixAt stride field (writeField stride store ptr i f (field values[i] f))
      ptr values (stride*i+f+1) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · simpa only [writeField_pages] using h.2.1
  · apply (read64_write64_disjoint store.mem _ _ ptr.toUInt32 ?_).trans h.2.2.1
    left
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by have := h.1; omega), fieldAddress_toNat h.1 hi hf]
    omega
  · intro j hj g hg hPrefix
    by_cases heq : stride*j+g = stride*i+f
    · obtain ⟨rfl, rfl⟩ := field_index_injective hg hf heq
      exact read64_write64 ..
    · apply (read64_write64_disjoint store.mem _ _ _ ?_).trans (h.2.2.2 j hj g hg (by omega))
      rw [fieldAddress_toNat h.1 hj hg, fieldAddress_toNat h.1 hi hf]
      omega

theorem writeField_frame (stride : Nat) (store : Store Unit) (ptr : UInt64)
    (size i f : Nat) (value : UInt64)
    (hFit : ptr.toNat+8*(stride*size+1) ≤ 4294967296) (hi : i < size) (hf : f < stride) :
    WritesRange store (writeField stride store ptr i f value)
      ptr.toNat (ptr.toNat+8*(stride*size+1)) := by
  have := field_index_lt hi hf
  apply WritesRange.write64
  · rw [fieldAddress_toNat hFit hi hf]
    omega
  · rw [fieldAddress_toNat hFit hi hf]
    omega

#print axioms PrefixAt.complete
#print axioms PrefixAt.fieldBound
#print axioms PrefixAt.write_next
#print axioms writeField_frame
end Project.ProofKit.FixedWidthArray
