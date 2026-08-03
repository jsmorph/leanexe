import Project.SharedPair.Base
import Project.SharedPair.Frame
import Project.WpScaffold

/-!
# Shared-pair byte-copy loop

The loop-body theorem accepts the loop rule's postcondition as a parameter.
Its statement exposes only invariant restoration, measure decrease, and exit.
-/

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

private theorem copyNotLe (bytes : List UInt8) (k : Nat)
    (hLen : bytes.length + 1 < 4294967296)
    (hklt : k < bytes.length) :
    ¬ (UInt64.ofNat k ≥ UInt64.ofNat bytes.length) := by
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length := by
    u64_omega
  rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
  omega

private def copyBodyProg : Wasm.Program :=
  [.localGet 16, .localGet 12, .geUI64, .br_if 1, .localGet 14,
    .localGet 16, .addI64, .wrapI64, .localGet 11,
    .localGet 16, .addI64, .wrapI64, .load8U 0, .store8 0,
    .localGet 16, .constI64 1, .addI64, .localSet 16, .br 0]

/-- The copy-loop body obligation, generic over the loop rule's
postcondition so no continuation appears in any statement.  The
repeat premise takes the re-established invariant and measure
decrease; the exit premise takes the exit state by equation. -/
theorem copyBody (env : HostEnv Unit) (st1 st2 : Store Unit)
    (ptr g0 g2 : UInt64) (bytes : List UInt8) (k : Nat)
    (POST : Assertion Unit) (m0 : Nat)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hInput : BytesAt st1 ptr bytes)
    (hk : k ≤ bytes.length)
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hlo : ∀ a < g0.toNat, st2.mem.bytes a = st1.mem.bytes a)
    (hpref : ∀ i < k, st2.mem.bytes (g0.toNat + 48 + i) = bytes[i]!)
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh16 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
      allocSizeU (UInt64.ofNat bytes.length))
    (hh24 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) =
      0)
    (hm0 : bytes.length - k = m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hRepeat : ∀ (st' : Store Unit) (s' : Locals),
      vInv st1 ptr g0 g2 bytes st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } ∧
      vMeasure bytes st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } <
        m0 →
      POST (.Break 0 st' s'))
    (hExit : ∀ (st' : Store Unit) (s' : Locals),
      k = bytes.length ∧ st' = st2 ∧
      s' = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k) (allocSizeU (UInt64.ofNat bytes.length)) 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48) →
      POST (.Break 1 st' s'))
    (sB : Locals)
    (hsB : sB = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k) (allocSizeU (UInt64.ofNat bytes.length)) 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48)) :
    wp «module» copyBodyProg POST st2 sB env := by
  subst hsB
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  simp only [copyBodyProg]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  by_cases hkend : k = bytes.length
  swap
  · -- copy one byte and continue
    simp only [if_neg
      (copyNotLe bytes k hLen (Nat.lt_of_le_of_ne hk hkend))]
    try simp
    try simp only [hTrap, if_false, false_and, and_false]
    have hklt : k < bytes.length := Nat.lt_of_le_of_ne hk hkend
    obtain ⟨hread, hbound⟩ := hInput k hklt
    have hsrcN : (ptr + UInt64.ofNat k).toNat = ptr.toNat + k := by
      rw [UInt64.toNat_add, hkU]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsrc32 : (ptr + UInt64.ofNat k).toUInt32 =
        UInt32.ofNat ((ptr.toNat + k) % 4294967296) := by
      rw [toUInt32_eq_ofNat, hsrcN]
    rw [hsrc32] at hread hbound
    rw [toUInt32_ofNat_mod_toNat] at hbound
    have hkadd : (UInt64.ofNat k + 1) = UInt64.ofNat (k + 1) := by
      apply UInt64.toNat.inj
      rw [toNat_add_one, hkU, toNat_ofNat_lt (by rw [size_eq]; omega)]
      rw [hkU]
      rw [size_eq]
      omega
    have hreadval : st2.mem.read8
        (UInt32.ofNat ((ptr.toNat + k) % 4294967296)) = bytes[k]! := by
      rw [Mem.read8, toUInt32_ofNat_mod_toNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [hlo (ptr.toNat + k) (by omega)]
      have hthis := hread
      rw [Mem.read8, toUInt32_ofNat_mod_toNat,
        Nat.mod_eq_of_lt (by omega)] at hthis
      exact hthis
    rw [hreadval]
    refine ⟨by omega, by omega,
      hRepeat _ _ ⟨⟨k + 1, hklt, ?_, hpg, hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
    · rw [← hkadd]
      simp [vFrame]
    · intro a ha
      rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
      exact hlo a ha
    · intro i hi
      by_cases hieq : i = k
      · subst hieq
        rw [write8_bytes_hit _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
      · rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
        exact hpref i (by omega)
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh0
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh8
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh16
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh24
    · simp [vMeasure]
      omega

  · -- all bytes copied: take the exit branch
    have hle : (UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k) := by
      rw [UInt64.le_iff_toNat_le, hkU, hlenU]
      omega
    have hge : UInt64.ofNat k ≥ UInt64.ofNat bytes.length := hle
    rw [if_pos hge]
    try simp
    try simp only [hTrap, if_false, false_and, and_false]
    exact hExit _ _ ⟨hkend, rfl, rfl⟩


end Project.SharedPair.Spec
