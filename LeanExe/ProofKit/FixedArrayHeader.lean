import LeanExe.Common
import LeanExe.ProofKit.Memory
import LeanExe.ProofKit.Allocation

namespace LeanExe.ProofKit

open Wasm

def FreshFixedArrayAt (st : Store Unit) (ptr capacity stride : UInt64) : Prop :=
  st.mem.read64 ((ptr - 48).toUInt32) = 5501223100278326855 ∧
  st.mem.read64 ((ptr - 40).toUInt32) = 1 ∧
  st.mem.read64 ((ptr - 32).toUInt32) = capacity ∧
  st.mem.read64 ((ptr - 24).toUInt32) = 2 ∧
  st.mem.read64 ((ptr - 16).toUInt32) = stride ∧
  st.mem.read64 ((ptr - 8).toUInt32) = 0

theorem FreshFixedArrayAt.frame {st st' : Store Unit}
    {ptr capacity stride base : UInt64}
    (hPtr32 : ptr.toNat < 4294967296)
    (hHeader : 48 ≤ ptr.toNat) (hBelow : ptr.toNat ≤ base.toNat)
    (hBytes : ∀ a : Nat, a < base.toNat →
      st'.mem.bytes a = st.mem.bytes a)
    (hFresh : FreshFixedArrayAt st ptr capacity stride) :
    FreshFixedArrayAt st' ptr capacity stride := by
  have hRead (offset : UInt64) (hOffset : offset.toNat ≤ 48)
      (hOffset8 : 8 ≤ offset.toNat) :
      st'.mem.read64 ((ptr - offset).toUInt32) =
        st.mem.read64 ((ptr - offset).toUInt32) := by
    apply LeanExe.Common.read64_congr
    intro i hi
    rw [LeanExe.Common.toUInt32_toNat,
      LeanExe.Common.toNat_sub_le ptr offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact hBytes _ (by omega)
  obtain ⟨h48, h40, h32, h24, h16, h8⟩ := hFresh
  exact ⟨(hRead 48 (by decide) (by decide)).trans h48,
    (hRead 40 (by decide) (by decide)).trans h40,
    (hRead 32 (by decide) (by decide)).trans h32,
    (hRead 24 (by decide) (by decide)).trans h24,
    (hRead 16 (by decide) (by decide)).trans h16,
    (hRead 8 (by decide) (by decide)).trans h8⟩

def fixedArrayHeaderMem (mem : Mem) (base capacity stride : UInt64) : Mem :=
  (((((mem.write64
    (UInt32.ofNat (base.toNat % 4294967296)) 5501223100278326855).write64
    (UInt32.ofNat ((base.toNat + 8) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 16) % 4294967296)) capacity).write64
    (UInt32.ofNat ((base.toNat + 24) % 4294967296)) 2).write64
    (UInt32.ofNat ((base.toNat + 32) % 4294967296)) stride).write64
    (UInt32.ofNat ((base.toNat + 40) % 4294967296)) 0

def fixedArrayAllocBumpStore (st : Store Unit) (base capacity stride : UInt64) :
    Store Unit :=
  { st with
    globals := { globals :=
      st.globals.globals.set 0 (.i64 (base + 48 + capacity)) }
    mem := fixedArrayHeaderMem st.mem base capacity stride }

theorem fixedArrayAllocBumpStore_pages (st : Store Unit)
    (base capacity stride : UInt64) :
    (fixedArrayAllocBumpStore st base capacity stride).mem.pages =
      st.mem.pages := by
  simp [fixedArrayAllocBumpStore, fixedArrayHeaderMem, Mem.write64_pages]

end LeanExe.ProofKit

namespace LeanExe.ProofKit.FixedArrayHeader
open Wasm LeanExe.ProofKit.Memory LeanExe.ProofKit.Allocation

theorem reads (mem : Mem) (base capacity stride : UInt64) :
    let written := fixedArrayHeaderMem mem base capacity stride
    written.read64 (UInt32.ofNat (base.toNat % 4294967296)) = 5501223100278326855 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 8) % 4294967296)) = 1 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 16) % 4294967296)) = capacity ∧
    written.read64 (UInt32.ofNat ((base.toNat + 24) % 4294967296)) = 2 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 32) % 4294967296)) = stride ∧
    written.read64 (UInt32.ofNat ((base.toNat + 40) % 4294967296)) = 0 := by
  dsimp only
  unfold fixedArrayHeaderMem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat first
      | rw [read64_write64_disjoint _ _ _ _ (by
          simp only [UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_mod]
          omega)]
      | exact read64_write64 ..

theorem fresh (store : Store Unit) (base capacity stride : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) :
    FreshFixedArrayAt { store with mem := fixedArrayHeaderMem store.mem base capacity stride }
      (base + 48) capacity stride := by
  obtain ⟨h40, h32, h24, h16, h8⟩ := headerOffsets base hFit32
  have h48 : (base + 48 - 48).toNat = base.toNat := by
    rw [root_sub_toNat base 48 hFit32 (by decide)]
    rfl
  simpa only [FreshFixedArrayAt, toUInt32_eq_ofNat, h48, h40, h32, h24, h16, h8]
    using reads store.mem base capacity stride

theorem from_root (mem : Mem) (root capacity stride : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296) :
    fixedArrayHeaderMem mem (root - 48) capacity stride =
      (((((mem.write64 (root - 48).toUInt32 5501223100278326855).write64
        (root - 40).toUInt32 1).write64 (root - 32).toUInt32 capacity).write64
        (root - 24).toUInt32 2).write64 (root - 16).toUInt32 stride).write64
        (root - 8).toUInt32 0 := by
  have hFit : (root - 48).toNat + 48 ≤ 4294967296 := by
    rw [toNat_sub_of_le root 48 hRoot]
    change root.toNat - 48 + 48 ≤ 4294967296
    omega
  obtain ⟨h40, h32, h24, h16, h8⟩ := headerOffsets (root - 48) hFit
  simp only [UInt64.sub_add_cancel] at h40 h32 h24 h16 h8
  simp only [fixedArrayHeaderMem, toUInt32_eq_ofNat, h40, h32, h24, h16, h8]

theorem bytes_outside (mem : Mem) (base capacity stride : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (fixedArrayHeaderMem mem base capacity stride).bytes address = mem.bytes address := by
  unfold fixedArrayHeaderMem
  repeat rw [write64_bytes_outside _ _ _ (by
    simp only [UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_mod]
    omega)]

#print axioms reads
#print axioms fresh
#print axioms from_root
#print axioms bytes_outside

end LeanExe.ProofKit.FixedArrayHeader
