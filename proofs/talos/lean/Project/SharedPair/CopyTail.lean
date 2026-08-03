import Project.SharedPair.CopyBody
import Project.Runtime.ArrayConstruction

/-!
# Shared-pair allocation and retain tail

The theorem starts after the second allocator's empty-free-list loop exits.
It proves the allocation, array-cell writes, inline retain, and result package.
-/

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

theorem copyBuildTail_correct
    (env : HostEnv Unit) (st1 st2 : Store Unit)
    (ptr g0 g2 g3 : UInt64) (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hg1 : st1.globals.globals[1]? = some (.i64 0))
    (hg2 : st1.globals.globals[2]? = some (.i64 g2))
    (hg3 : st1.globals.globals[3]? = some (.i64 g3))
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hlo : ∀ a < g0.toNat, st2.mem.bytes a = st1.mem.bytes a)
    (hpref : ∀ i < bytes.length,
      st2.mem.bytes (g0.toNat + 48 + i) = bytes[i]!)
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hglen : 3 < st1.globals.globals.length)
    (hg0len : 0 < st1.globals.globals.length)
    (hg2len : 2 < st1.globals.globals.length)
    (hg1S : st2.globals.globals[1]? = some (.i64 0)) :
    wp «module» copyBuildTail (copyPost st1 ptr g0 g2 g3 bytes)
      { st2 with mem := (st2.mem.write8
        (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296)) 33) }
      (vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56
        0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
          65536 + 1)
        0) env := by
  unfold copyBuildTail copyPost copyResult
  simp only [Project.SharedPair.func0, List.drop]
  have PA := Project.Runtime.ArrayConstruction.allocationArith
    allocSize allocSizeU st1 g0 bytes hFit32 h17 hsub40 hg0_32 hlenU hszU
    hszN_ge hszN_ge8 hFit hPages
  wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  set stB : Store Unit := { st2 with mem := (st2.mem.write8
    (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
    33) } with hstB
  have hg0S : stB.globals.globals[0]? =
      some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    rw [List.getElem?_set, List.getElem?_set]
    simp only [if_neg (by omega : ¬ (2 = 0)),
      if_pos (rfl : (0 : Nat) = 0)]
    simp [hg0len]
  wp_run_big
  try simp only [hg0S]
  try wp_run_big
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [PA.2.2.1])]
  wp_run_big
  try simp
  have hpgB : stB.mem.pages = st1.mem.pages := by
    rw [hstB]
    dsimp only
    rw [write8_pages, hpg]
  try simp only [hpgB]
  try wp_run_big
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [PA.2.2.2.2.2.2.2.1])]
  wp_run_big
  try simp only [hg0S]
  try wp_run_big
  try simp
  try simp only [hg0S]
  try wp_run_big
  try simp
  rw [PA.2.2.2.2.2.2.2.2.2.1,
    PA.2.2.2.2.2.2.2.2.2.2.1,
    PA.2.2.2.2.2.2.2.2.2.2.2.1,
    PA.2.2.2.2.2.2.2.2.2.2.2.2.1,
    PA.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    ?_⟩
  have hg2S : stB.globals.globals[2]? = some (.i64 (g2 + 1)) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    rw [List.getElem?_set]
    simp [hg2len]
  simp only [hg2S]
  try wp_run_big
  try simp
  refine ⟨by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_⟩
  simp only [PA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hB0 : stB.mem.read64
      (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855 := by
    rw [hstB]
    dsimp only
    rw [read64_write8_ne _ _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hh0
  have hB8 : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
    rw [hstB]
    dsimp only
    rw [read64_write8_ne _ _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hh8
  have PC := Project.Runtime.ArrayConstruction.arrayCells
    allocSize allocSizeU _ stB g0 bytes hFit32 hszU hszN_ge hszN_ge8
    hg0_32 hB0 hB8 rfl
  simp only [PC.1]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [PA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])]
  wp_run_big
  try simp
  have hmagic2e := PC.2.1
  rw [hstB] at hmagic2e
  dsimp only at hmagic2e
  try simp only [PC.2.1, hmagic2e]
  try wp_run_big
  try simp
  refine ⟨by omega, ?_⟩
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_big
  try simp
  refine ⟨by omega, ?_⟩
  have hrc2e := PC.2.2
  rw [show (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) =
      (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) from by
    rw [hsub40]] at hrc2e
  rw [hstB] at hrc2e
  have hrc2d := hrc2e
  dsimp only at hrc2d
  rw [hrc2e]
  try wp_run_big
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by decide)]
  wp_run_big
  have hg3S : ((stB.globals.globals.set 0
      (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
        48 + 56))).set 2 (Value.i64 (g2 + 1 + 1)))[3]? =
      some (Value.i64 g3) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    simp [List.getElem?_set, hglen]
    exact (List.getElem?_eq_some_iff.mp hg3).choose_spec
  try simp only [hg3S]
  try wp_run_big
  try simp
  have hlenB : stB.globals.globals.length =
      st1.globals.globals.length := by
    rw [hstB]
    dsimp only
    rw [hgl]
    simp
  have h0B : 0 < stB.globals.globals.length := by omega
  have h2B : 2 < stB.globals.globals.length := by omega
  have h3B : 3 < stB.globals.globals.length := by omega
  have haddr40 : (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) =
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
    rw [hsub40]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [func0Def]
  · simp [List.getElem?_set, h0B]
  · rw [hstB]
    dsimp only
    exact hg1S
  · simp [List.getElem?_set, h2B]
  · simp [List.getElem?_set, h3B]
  · rw [haddr40, Mem.read64_write64_same]
  · intro i hi
    rw [write64_bytes_ne _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    rw [write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    rw [hstB]
    dsimp only
    by_cases hieq : i = bytes.length
    · subst hieq
      rw [write8_bytes_hit _ _ _
        (by rw [toUInt32_ofNat_mod_toNat]; omega)]
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    · have hilt : i < bytes.length := by omega
      rw [write8_bytes_ne _ _ _
        (by rw [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hpref i hilt, getBang_eq hilt]
      rw [List.getElem?_append_left hilt, List.getElem?_eq_getElem hilt]
      simp
  · intro a ha
    rw [write64_bytes_lo _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    rw [write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    rw [hstB]
    dsimp only
    rw [write8_bytes_ne _ _ _
      (by rw [toUInt32_ofNat_mod_toNat]; omega)]
    exact hlo a ha

end Project.SharedPair.Spec
