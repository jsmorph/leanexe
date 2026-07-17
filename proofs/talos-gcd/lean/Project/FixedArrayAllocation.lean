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

def fixedArrayHeaderMem (mem : Mem) (base capacity stride : UInt64) : Mem :=
  (((((mem.write64
    (UInt32.ofNat (base.toNat % 4294967296)) 5501223100278326855).write64
    (UInt32.ofNat ((base.toNat + 8) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 16) % 4294967296)) capacity).write64
    (UInt32.ofNat ((base.toNat + 24) % 4294967296)) 2).write64
    (UInt32.ofNat ((base.toNat + 32) % 4294967296)) stride).write64
    (UInt32.ofNat ((base.toNat + 40) % 4294967296)) 0

def fixedArrayMem (mem : Mem) (base capacity stride length : UInt64) : Mem :=
  (fixedArrayHeaderMem mem base capacity stride).write64
    (UInt32.ofNat ((base.toNat + 48) % 4294967296)) length

abbrev emptyFixedArrayMem (mem : Mem) (base capacity stride : UInt64) : Mem :=
  fixedArrayMem mem base capacity stride 0

theorem fixedArrayHeaderMem_spec (st : Store Unit)
    (base capacity stride : UInt64)
    (hFit32 : base.toNat + 56 < 4294967296) :
    FreshFixedArrayAt { st with
      mem := fixedArrayHeaderMem st.mem base capacity stride }
      (base + 48) capacity stride := by
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
  unfold FreshFixedArrayAt fixedArrayHeaderMem
  simp only [toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24,
    hsub16, hsub8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> read_frames

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
  unfold FreshFixedArrayAt emptyFixedArrayMem fixedArrayMem
    fixedArrayHeaderMem
  simp only [toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16,
    hsub8, hbase48]
  read_frames
  simp

theorem fixedArrayHeaderMem_bytes_before (mem : Mem)
    (base capacity stride : UInt64) (a : Nat)
    (hFit32 : base.toNat + 48 < 4294967296) (ha : a < base.toNat) :
    (fixedArrayHeaderMem mem base capacity stride).bytes a = mem.bytes a := by
  unfold fixedArrayHeaderMem
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
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]

theorem fixedArrayMem_bytes_before (mem : Mem)
    (base capacity stride length : UInt64) (a : Nat)
    (hFit32 : base.toNat + 56 < 4294967296) (ha : a < base.toNat) :
    (fixedArrayMem mem base capacity stride length).bytes a = mem.bytes a := by
  unfold fixedArrayMem fixedArrayHeaderMem
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

theorem emptyFixedArrayMem_bytes_before (mem : Mem)
    (base capacity stride : UInt64) (a : Nat)
    (hFit32 : base.toNat + 56 < 4294967296) (ha : a < base.toNat) :
    (emptyFixedArrayMem mem base capacity stride).bytes a = mem.bytes a := by
  exact fixedArrayMem_bytes_before mem base capacity stride 0 a hFit32 ha

theorem fixedArrayBumpRoot_toNat (base : UInt64)
    (hBound : base.toNat + 48 < UInt64.size) :
    (base + 48).toNat = base.toNat + 48 := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt hBound

theorem fixedArrayBumpRoot_sub_toNat (base offset : UInt64)
    (hRoot : (base + 48).toNat = base.toNat + 48)
    (hOffset : offset.toNat ≤ 48) :
    (base + 48 - offset).toNat = base.toNat + 48 - offset.toNat := by
  rw [toNat_sub_le _ _ (by rw [hRoot]; omega), hRoot]

theorem fixedArrayBumpTop_sub_one_toNat (base need : UInt64)
    (hTop : (base + 48 + need).toNat =
      base.toNat + 48 + need.toNat) :
    (base + 48 + need - 1).toNat =
      base.toNat + 48 + need.toNat - 1 := by
  rw [toNat_sub_le _ _ (by rw [hTop]; simp; omega), hTop]
  rfl

theorem fixedArrayBumpPages_toNat (base need : UInt64)
    (hTop : (base + 48 + need).toNat =
      base.toNat + 48 + need.toNat)
    (hBound : base.toNat + 48 + need.toNat < UInt64.size) :
    ((base + 48 + need - 1) / 65536 + 1).toNat =
      (base.toNat + 48 + need.toNat - 1) / 65536 + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_div,
    fixedArrayBumpTop_sub_one_toNat base need hTop]
  have h65536 : (65536 : UInt64).toNat = 65536 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hSize : UInt64.size = 18446744073709551616 := rfl
  rw [hSize] at hBound
  rw [h65536, h1]
  omega

theorem fixedArrayMemorySize_toNat (pages : Nat) (hPages : pages ≤ 65536) :
    ((UInt32.ofNat pages).toUInt64).toNat = pages := by
  have hlt : pages < UInt32.size := by
    have hSize : UInt32.size = 4294967296 := rfl
    omega
  have hnat : (UInt32.ofNat pages).toNat = pages :=
    UInt32.toNat_ofNat_of_lt' hlt
  simp [hnat]

theorem fixedArrayBump_no_grow (base need : UInt64) (pages : Nat)
    (hTop : (base + 48 + need).toNat =
      base.toNat + 48 + need.toNat)
    (hFit : base.toNat + 48 + need.toNat ≤ pages * 65536)
    (hPages : pages ≤ 65536) :
    ¬((UInt32.ofNat pages).toUInt64 <
      (base + 48 + need - 1) / 65536 + 1) := by
  have hBound : base.toNat + 48 + need.toNat < UInt64.size := by
    have hSize : UInt64.size = 18446744073709551616 := rfl
    omega
  rw [UInt64.lt_iff_toNat_lt, fixedArrayMemorySize_toNat pages hPages,
    fixedArrayBumpPages_toNat base need hTop hBound]
  omega

end Project.Clob
