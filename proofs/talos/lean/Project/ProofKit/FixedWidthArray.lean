import Project.ProofKit.ArrayPrefix
import Project.ProofKit.ArrayField

namespace Project.ProofKit.FixedWidthArray
open Wasm Memory UInt64Array

def At (stride : Nat) (field : α → Nat → UInt64)
    (store : Store Unit) (ptr : UInt64) (values : Array α) : Prop :=
  ptr.toNat + 8*(stride*values.size+1) ≤ 4294967296 ∧
  ptr.toNat + 8*(stride*values.size+1) ≤ store.mem.pages*65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size ∧
  ∀ (i : Nat) (hi : i < values.size) (f : Nat), f < stride →
    store.mem.read64 (wordAddress ptr (stride*i+f+1)) = field values[i] f

theorem field_index_lt {stride size i f : Nat} (hi : i < size) (hf : f < stride) :
    stride*i+f < stride*size := by
  have h := Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at h
  omega

theorem field_index_injective {stride i j f g : Nat} (hf : f < stride) (hg : g < stride)
    (h : stride*i+f = stride*j+g) : i = j ∧ f = g := by
  have hDiv := congrArg (· / stride) h
  simp only [Nat.mul_add_div (by omega : 0 < stride), Nat.div_eq_of_lt hf,
    Nat.div_eq_of_lt hg, Nat.add_zero] at hDiv
  refine ⟨hDiv, ?_⟩
  rw [hDiv] at h
  exact Nat.add_left_cancel h

theorem At.size_lt {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field store ptr values)
    (hStride : 0 < stride) : values.size < UInt64.size := by
  have hSize := Nat.le_mul_of_pos_left values.size hStride
  have hBound := h.1
  change values.size < 18446744073709551616
  omega

theorem At.pointerAddress_toNat {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field store ptr values) :
    ptr.toUInt32.toNat = ptr.toNat := by
  rw [toUInt32_toNat, Nat.mod_eq_of_lt (by have := h.1; omega)]

theorem At.lengthRead {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field store ptr values) :
    store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size := h.2.2.1

theorem At.lengthBound {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field store ptr values) :
    ptr.toUInt32.toNat + 8 ≤ store.mem.pages*65536 := by
  rw [h.pointerAddress_toNat]
  have := h.2.1
  omega

theorem fieldAddress_toNat {stride : Nat} {ptr : UInt64} {size i f : Nat}
    (hFit : ptr.toNat + 8*(stride*size+1) ≤ 4294967296)
    (hi : i < size) (hf : f < stride) :
    (wordAddress ptr (stride*i+f+1)).toNat = ptr.toNat + 8*(stride*i+f+1) :=
  wordAddress_toNat hFit (by have := field_index_lt hi hf; omega)

theorem At.fieldBound {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field store ptr values)
    (i f : Nat) (hi : i < values.size) (hf : f < stride) :
    (wordAddress ptr (stride*i+f+1)).toNat + 8 ≤ store.mem.pages*65536 := by
  rw [fieldAddress_toNat h.1 hi hf]
  have := field_index_lt hi hf
  have := h.2.1
  omega

theorem At.fieldRead {stride : Nat} {field : α → Nat → UInt64} {store : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field store ptr values)
    (i f : Nat) (hi : i < values.size) (hf : f < stride) :
    store.mem.read64 (wordAddress ptr (stride*i+f+1)) = field values[i] f := h.2.2.2 i hi f hf

theorem generatedFieldAddress (ptr : UInt64) (stride i f : Nat) :
    UInt32.ofNat ((ptr+(UInt64.ofNat i*UInt64.ofNat stride+UInt64.ofNat (f+1))*8).toNat % 2^32) =
      wordAddress ptr (stride*i+f+1) := by
  rw [ArrayField.field_word]
  exact (toUInt32_eq_ofNat _).symm

theorem At.frame {stride : Nat} {field : α → Nat → UInt64} {initial final : Store Unit}
    {ptr : UInt64} {values : Array α} (h : At stride field initial ptr values)
    (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address, ptr.toNat ≤ address → address < ptr.toNat+8*(stride*values.size+1) →
      final.mem.bytes address = initial.mem.bytes address) : At stride field final ptr values := by
  refine ⟨h.1, h.2.1.trans (Nat.mul_le_mul_right 65536 hPages), ?_, ?_⟩
  · apply (read64_congr ptr.toUInt32 ?_).trans h.lengthRead
    intro byte hByte
    apply hBytes <;> rw [h.pointerAddress_toNat] <;> omega
  · intro i hi f hf
    have := field_index_lt hi hf
    apply (read64_congr _ ?_).trans (h.fieldRead i f hi hf)
    intro byte hByte
    apply hBytes <;> rw [fieldAddress_toNat h.1 hi hf] <;> omega

theorem At.writesRange {stride : Nat} {field : α → Nat → UInt64} {initial final : Store Unit}
    {ptr : UInt64} {values : Array α} {start stop : Nat} (h : At stride field initial ptr values)
    (hWrites : WritesRange initial final start stop)
    (hSep : ptr.toNat+8*(stride*values.size+1) ≤ start ∨ stop ≤ ptr.toNat) :
    At stride field final ptr values :=
  h.frame hWrites.2.1.ge (fun _ hLo hHi => hWrites.2.2 _ (by omega))

#print axioms field_index_injective
#print axioms At.size_lt
#print axioms At.fieldBound
#print axioms generatedFieldAddress
#print axioms At.frame
#print axioms At.writesRange
end Project.ProofKit.FixedWidthArray
