import Project.Common

/-!
# Array-construction arithmetic and memory facts

These lemmas describe the runtime allocator's address calculations and the
memory facts preserved by the object-header and array-cell write sequence.
The allocation-size functions are parameters because generated proofs use
both natural-number and `UInt64` forms of the same policy.
-/

namespace Project.Runtime.ArrayConstruction

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

private theorem addressMods (allocSize : Nat → Nat)
    (allocSizeU : UInt64 → UInt64) (g0 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1)) :
    (g0.toNat) % 4294967296 = g0.toNat ∧
    (g0.toNat + 8) % 4294967296 = g0.toNat + 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Nat.mod_eq_of_lt (by omega)

theorem arrayCells (allocSize : Nat → Nat)
    (allocSizeU : UInt64 → UInt64) (M : Mem) (stB : Store Unit)
    (g0 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hg0_32 : g0.toNat < 4294967296)
    (hB0 : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hB8 : stB.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hM : M = (((((((((((((stB.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296)) 56).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296)) (UInt64.ofNat bytes.length + 1)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296)) (UInt64.ofNat bytes.length + 1))) :
    M.read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) = g0 + 48 ∧
    M.read64 (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
  subst hM
  refine ⟨?_, ?_, ?_⟩
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hB0
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hB8

theorem allocationArith (allocSize : Nat → Nat)
    (allocSizeU : UInt64 → UInt64) (st1 : Store Unit) (g0 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hg0_32 : g0.toNat < 4294967296)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536) :
    (48 : UInt64).toNat = 48 ∧
    (18446744073709551616 : Nat) = UInt64.size ∧
    ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 < g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) - 1 ∧
    ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1).toNat = (g0.toNat + 152 + allocSize (bytes.length + 1) - 1) / 65536 + 1 ∧
    ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1 ≤ UInt64.ofNat (st1.mem.pages % 4294967296) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 40).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 32).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 24).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 16).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 8).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 18446744073709551616 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat ∧
    ¬ ((g0 + 48 : UInt64) = 0) ∧
    (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) = (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
  have h48 : (48 : UInt64).toNat = 48 :=
    rfl
  have hs : (18446744073709551616 : Nat) = UInt64.size :=
    rfl
  have hno_wrap2 : ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 < g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add, h17]
    have ha : (48 : UInt64).toNat = 48 := rfl
    have hb : (56 : UInt64).toNat = 56 := rfl
    rw [ha, hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have h17b : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, h17]
    have ha : (48 : UInt64).toNat = 48 := rfl
    have hb : (56 : UInt64).toNat = 56 := rfl
    rw [ha, hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsub1b : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) - 1 := by
    rw [UInt64.toNat_sub, h17b]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    omega
  have hpn2 : ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1).toNat = (g0.toNat + 152 + allocSize (bytes.length + 1) - 1) / 65536 + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_div, hsub1b]
    have h65536 : (65536 : UInt64).toNat = 65536 := rfl
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h65536, h1]
    omega
  have hp32b : ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages := by
    have hlt : st1.mem.pages < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    have h1 : (UInt32.ofNat st1.mem.pages).toNat = st1.mem.pages :=
      UInt32.toNat_ofNat_of_lt' hlt
    simp [h1]
  have hgeM : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1 ≤ UInt64.ofNat (st1.mem.pages % 4294967296) := by
    rw [UInt64.le_iff_toNat_le, hpn2,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    omega
  have hB48 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, h17]
    have ha : (48 : UInt64).toNat = 48 := rfl
    rw [ha]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB40 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 40).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (40 : UInt64).toNat = 40 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB32 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 32).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (32 : UInt64).toNat = 32 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB24 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 24).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (24 : UInt64).toNat = 24 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB16 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 16).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (16 : UInt64).toNat = 16 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB8 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 8).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (8 : UInt64).toNat = 8 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hXmod : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 18446744073709551616 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hpne : ¬ ((g0 + 48 : UInt64) = 0) := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_add] at this
    have hc : (48 : UInt64).toNat = 48 := rfl
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [hc, h0] at this
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have haddr40 : (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) = (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
    rw [hsub40]
  exact ⟨h48, hs, hno_wrap2, h17b, hsub1b, hpn2, hp32b, hgeM, hB48, hsubB40, hsubB32, hsubB24, hsubB16, hsubB8, hXmod, hpne, haddr40⟩

end Project.Runtime.ArrayConstruction
