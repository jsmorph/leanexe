import Project.ProofKit.Memory

namespace Project.ProofKit.Allocation

open Project.ProofKit.Memory

theorem root_toNat (base : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) :
    (base + 48).toNat = base.toNat + 48 := by
  rw [UInt64.toNat_add]
  have h48 : (48 : UInt64).toNat = 48 := rfl
  rw [h48, Nat.mod_eq_of_lt]
  have hSize : UInt64.size = 18446744073709551616 := rfl
  omega

theorem top_toNat (base capacity : UInt64)
    (hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296) :
    (base + 48 + capacity).toNat = base.toNat + 48 + capacity.toNat := by
  rw [UInt64.toNat_add, root_toNat base (by omega), Nat.mod_eq_of_lt]
  have hSize : UInt64.size = 18446744073709551616 := rfl
  omega

theorem top_not_lt_base (base capacity : UInt64)
    (hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296) :
    ¬(base + 48 + capacity < base) := by
  rw [UInt64.lt_iff_toNat_lt, top_toNat base capacity hFit32]
  omega

theorem root_toUInt32 (base : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) :
    (base + 48).toUInt32 =
      UInt32.ofNat ((base.toNat + 48) % 4294967296) := by
  rw [toUInt32_eq_ofNat, root_toNat base hFit32]

theorem top_toUInt32 (base capacity : UInt64)
    (hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296) :
    (base + 48 + capacity).toUInt32 =
      UInt32.ofNat ((base.toNat + 48 + capacity.toNat) % 4294967296) := by
  rw [toUInt32_eq_ofNat, top_toNat base capacity hFit32]

theorem root_sub_toNat (base offset : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hOffset : offset.toNat ≤ 48) :
    (base + 48 - offset).toNat = base.toNat + 48 - offset.toNat := by
  rw [toNat_sub_of_le _ _ (by rw [root_toNat base hFit32]; omega),
    root_toNat base hFit32]

theorem headerOffsets (base : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) :
    (base + 48 - 40).toNat = base.toNat + 8 ∧
    (base + 48 - 32).toNat = base.toNat + 16 ∧
    (base + 48 - 24).toNat = base.toNat + 24 ∧
    (base + 48 - 16).toNat = base.toNat + 32 ∧
    (base + 48 - 8).toNat = base.toNat + 40 := by
  have h40 := root_sub_toNat base 40 hFit32 (by decide)
  have h32 := root_sub_toNat base 32 hFit32 (by decide)
  have h24 := root_sub_toNat base 24 hFit32 (by decide)
  have h16 := root_sub_toNat base 16 hFit32 (by decide)
  have h8 := root_sub_toNat base 8 hFit32 (by decide)
  have h40Nat : (40 : UInt64).toNat = 40 := rfl
  have h32Nat : (32 : UInt64).toNat = 32 := rfl
  have h24Nat : (24 : UInt64).toNat = 24 := rfl
  have h16Nat : (16 : UInt64).toNat = 16 := rfl
  have h8Nat : (8 : UInt64).toNat = 8 := rfl
  rw [h40Nat] at h40
  rw [h32Nat] at h32
  rw [h24Nat] at h24
  rw [h16Nat] at h16
  rw [h8Nat] at h8
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem top_sub_one_toNat (base capacity : UInt64)
    (hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296) :
    (base + 48 + capacity - 1).toNat =
      base.toNat + 48 + capacity.toNat - 1 := by
  have hOne : (1 : UInt64).toNat = 1 := rfl
  rw [toNat_sub_of_le _ _ (by
      rw [top_toNat base capacity hFit32, hOne]
      omega),
    top_toNat base capacity hFit32, hOne]

theorem pagesNeeded_toNat (base capacity : UInt64)
    (hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296) :
    ((base + 48 + capacity - 1) / 65536 + 1).toNat =
      (base.toNat + 48 + capacity.toNat - 1) / 65536 + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_div,
    top_sub_one_toNat base capacity hFit32]
  have h65536 : (65536 : UInt64).toNat = 65536 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h65536, h1]
  have hSize : UInt64.size = 18446744073709551616 := rfl
  omega

theorem memoryPages_toNat (pages : Nat) (hPages : pages ≤ 65536) :
    ((UInt32.ofNat pages).toUInt64).toNat = pages := by
  have hlt : pages < UInt32.size := by
    have hSize : UInt32.size = 4294967296 := rfl
    omega
  have hNat : (UInt32.ofNat pages).toNat = pages :=
    UInt32.toNat_ofNat_of_lt' hlt
  simp [hNat]

theorem bump_no_grow (base capacity : UInt64) (pages : Nat)
    (hFit : base.toNat + 48 + capacity.toNat ≤ pages * 65536)
    (hPages : pages ≤ 65536) :
    ¬((UInt32.ofNat pages).toUInt64 <
      (base + 48 + capacity - 1) / 65536 + 1) := by
  have hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296 := by
    omega
  rw [UInt64.lt_iff_toNat_lt, memoryPages_toNat pages hPages,
    pagesNeeded_toNat base capacity hFit32]
  omega

structure BumpFacts (base capacity : UInt64) (pages : Nat) : Prop where
  fit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296
  rootToNat : (base + 48).toNat = base.toNat + 48
  topToNat : (base + 48 + capacity).toNat =
    base.toNat + 48 + capacity.toNat
  noOverflow : ¬(base + 48 + capacity < base)
  noGrow : ¬((UInt32.ofNat pages).toUInt64 <
    (base + 48 + capacity - 1) / 65536 + 1)
  headerOffsets :
    (base + 48 - 40).toNat = base.toNat + 8 ∧
    (base + 48 - 32).toNat = base.toNat + 16 ∧
    (base + 48 - 24).toNat = base.toNat + 24 ∧
    (base + 48 - 16).toNat = base.toNat + 32 ∧
    (base + 48 - 8).toNat = base.toNat + 40

theorem bumpFacts (base capacity : UInt64) (pages : Nat)
    (hFitMemory : base.toNat + 48 + capacity.toNat ≤ pages * 65536)
    (hPages : pages ≤ 65536) :
    BumpFacts base capacity pages := by
  have hFit32 : base.toNat + 48 + capacity.toNat ≤ 4294967296 := by
    omega
  exact {
    fit32 := hFit32
    rootToNat := root_toNat base (by omega)
    topToNat := top_toNat base capacity hFit32
    noOverflow := top_not_lt_base base capacity hFit32
    noGrow := bump_no_grow base capacity pages hFitMemory hPages
    headerOffsets := headerOffsets base (by omega) }

theorem BumpFacts.header40ToNat {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) :
    (base + 48 - 40).toNat = base.toNat + 8 :=
  h.headerOffsets.1

theorem BumpFacts.header32ToNat {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) :
    (base + 48 - 32).toNat = base.toNat + 16 :=
  h.headerOffsets.2.1

theorem BumpFacts.header24ToNat {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) :
    (base + 48 - 24).toNat = base.toNat + 24 :=
  h.headerOffsets.2.2.1

theorem BumpFacts.header16ToNat {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) :
    (base + 48 - 16).toNat = base.toNat + 32 :=
  h.headerOffsets.2.2.2.1

theorem BumpFacts.header8ToNat {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) :
    (base + 48 - 8).toNat = base.toNat + 40 :=
  h.headerOffsets.2.2.2.2

theorem BumpFacts.wordAddress_toNat {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) (word : Nat)
    (hWord : 8 * (word + 1) ≤ capacity.toNat) :
    (base + 48 + UInt64.ofNat (8 * word)).toUInt32.toNat =
      base.toNat + 48 + 8 * word := by
  simp only [Nat.mul_add, Nat.mul_one] at hWord
  have hFit32 := h.fit32
  have hCapacity := capacity.toNat_lt
  have hOffset : 8 * word < UInt64.size := by
    have hSize : UInt64.size = 18446744073709551616 := rfl
    omega
  have hAddress32 : base.toNat + 48 + 8 * word < 4294967296 := by
    omega
  have hAddress64 : base.toNat + 48 + 8 * word < 2 ^ 64 := by
    norm_num
    omega
  rw [toUInt32_toNat, UInt64.toNat_add, h.rootToNat,
    toNat_ofNat_lt hOffset, Nat.mod_eq_of_lt hAddress64,
    Nat.mod_eq_of_lt hAddress32]

theorem BumpFacts.wordAddress {base capacity : UInt64} {pages : Nat}
    (h : BumpFacts base capacity pages) (word : Nat)
    (hWord : 8 * (word + 1) ≤ capacity.toNat) :
    UInt32.ofNat
        (((base.toNat + 48) % 18446744073709551616 + 8 * word) %
          4294967296) =
      (base + 48 + UInt64.ofNat (8 * word)).toUInt32 := by
  simp only [Nat.mul_add, Nat.mul_one] at hWord
  have hFit32 := h.fit32
  have hRoot64 : base.toNat + 48 < 18446744073709551616 := by
    omega
  have hAddress32 : base.toNat + 48 + 8 * word < 4294967296 := by
    omega
  apply UInt32.toNat.inj
  rw [h.wordAddress_toNat word (by omega)]
  simp [Nat.mod_eq_of_lt hRoot64,
    Nat.mod_eq_of_lt hAddress32]

end Project.ProofKit.Allocation
