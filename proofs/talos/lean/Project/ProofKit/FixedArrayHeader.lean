import Project.FixedArrayAllocation
import Project.ProofKit.MemoryRoundtrip
import Project.ProofKit.Allocation

namespace Project.ProofKit.FixedArrayHeader
open Wasm Project.Clob Project.ProofKit.Memory Project.ProofKit.Allocation

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
#print axioms bytes_outside

end Project.ProofKit.FixedArrayHeader
