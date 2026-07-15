import Project.Clob

/-!
# Fixed-array allocation writes

Generated fixed-array allocations write six metadata words before the data
pointer and initialize the array length to zero.  This module names that memory
transformation and proves the resulting header.  CLOB branch proofs can use the
semantic result without repeating read-over-write normalization.
-/

namespace Project.Clob

open Wasm Project.Common

def emptyFixedArrayMem (mem : Mem) (base capacity stride : UInt64) : Mem :=
  ((((((mem.write64
    (UInt32.ofNat (base.toNat % 4294967296)) 5501223100278326855).write64
    (UInt32.ofNat ((base.toNat + 8) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 16) % 4294967296)) capacity).write64
    (UInt32.ofNat ((base.toNat + 24) % 4294967296)) 2).write64
    (UInt32.ofNat ((base.toNat + 32) % 4294967296)) stride).write64
    (UInt32.ofNat ((base.toNat + 40) % 4294967296)) 0).write64
    (UInt32.ofNat ((base.toNat + 48) % 4294967296)) 0

theorem emptyFixedArrayMem_spec (st : Store Unit) (base capacity stride : UInt64)
    (hFit32 : base.toNat + 56 < 4294967296) :
    FreshFixedArrayAt { st with
      mem := emptyFixedArrayMem st.mem base capacity stride }
      (base + 48) capacity stride ∧
    (emptyFixedArrayMem st.mem base capacity stride).read64
      (base + 48).toUInt32 = 0 := by
  have hbase48 : (base + 48).toNat = base.toNat + 48 := by
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    have hs : UInt64.size = 18446744073709551616 := rfl
    omega
  have hsub (offset : UInt64) (hOffset : offset.toNat ≤ 48) :
      (base + 48 - offset).toNat = base.toNat + 48 - offset.toNat := by
    rw [toNat_sub_le _ _ (by rw [hbase48]; omega), hbase48]
  have hsub48 : (base + 48 - 48).toNat = base.toNat := by
    rw [hsub 48 (by decide)]
    rfl
  have hsub40 : (base + 48 - 40).toNat = base.toNat + 8 := by
    rw [hsub 40 (by decide)]
    rfl
  have hsub32 : (base + 48 - 32).toNat = base.toNat + 16 := by
    rw [hsub 32 (by decide)]
    rfl
  have hsub24 : (base + 48 - 24).toNat = base.toNat + 24 := by
    rw [hsub 24 (by decide)]
    rfl
  have hsub16 : (base + 48 - 16).toNat = base.toNat + 32 := by
    rw [hsub 16 (by decide)]
    rfl
  have hsub8 : (base + 48 - 8).toNat = base.toNat + 40 := by
    rw [hsub 8 (by decide)]
    rfl
  unfold FreshFixedArrayAt emptyFixedArrayMem
  simp only [toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16,
    hsub8, hbase48]
  read_frames
  simp

theorem emptyFixedArrayMem_bytes_before (mem : Mem)
    (base capacity stride : UInt64) (a : Nat)
    (hFit32 : base.toNat + 56 < 4294967296) (ha : a < base.toNat) :
    (emptyFixedArrayMem mem base capacity stride).bytes a = mem.bytes a := by
  unfold emptyFixedArrayMem
  rw [write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    write64_bytes_lo _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]

end Project.Clob
