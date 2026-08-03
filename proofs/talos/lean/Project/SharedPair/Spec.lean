import Project.SharedPair.Copy

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576
@[proves Project.SharedPair.Spec.SharedPairSpec]
theorem sharedPushPair_correct : SharedPairSpec := by
  intro env st ptr g0 g2 g3 bytes hLen hPtr32 hBelow hFit32 hFit hPages
    hg0 hg1 hg2 hg3 hInput
  have hg0_32 : g0.toNat < 4294967296 := by
    have := hFit32
    unfold allocSize at this
    omega
  have hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1) := by
    unfold allocSize
    omega
  have hszN_ge8 : 8 ≤ allocSize (bytes.length + 1) := by
    unfold allocSize
    omega
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length := by u64_omega
  have hadd17 : (UInt64.ofNat bytes.length + 1 + 7).toNat = bytes.length + 8 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hlenU]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h7 : (7 : UInt64).toNat = 7 := rfl
    rw [h1, h7]
    omega
  have hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1) := by
    unfold allocSizeU allocSize
    rw [UInt64.toNat_mul, UInt64.toNat_div, hadd17]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    have : (bytes.length + 8) / 8 * 8 < 18446744073709551616 := by
      omega
    omega
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func0
    have hraw : ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8).toNat =
        allocSize (bytes.length + 1) := hszU
    have hnot_lt8 :
        ¬ ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8 < (8 : UInt64)) := by
      rw [UInt64.lt_iff_toNat_lt, hraw]
      have h8 : (8 : UInt64).toNat = 8 := rfl
      rw [h8]
      omega
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnot_lt8])]
    wp_run
    try simp only [hg1]
    try wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st1 s1 => st1 = st ∧
        s1 = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
          (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr
          (UInt64.ofNat bytes.length) 33 0 (UInt64.ofNat bytes.length + 1) 0
          (allocSizeU (UInt64.ofNat bytes.length)) 0 0 0 0 0)
      (μ := fun _ _ => 0)
    · constructor
      · rfl
      · simp [vFrame, allocSizeU]
    · rintro st1 s1 ⟨rfl, rfl⟩
      simp only [vFrame]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      try simp only [hg0]
      try wp_run
      have hno_wrap :
          ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) < g0) := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48, hszU]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hno_wrap])]
      wp_run
      simp
      have h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
          g0.toNat + 48 + allocSize (bytes.length + 1) := by
        rw [UInt64.toNat_add, UInt64.toNat_add, hszU]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub1 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1).toNat =
          g0.toNat + 48 + allocSize (bytes.length + 1) - 1 := by
        rw [UInt64.toNat_sub, h17]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1]
        omega
      have hpn : ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536
          + 1).toNat =
          (g0.toNat + 48 + allocSize (bytes.length + 1) - 1) / 65536 + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_div, hsub1]
        have h65536 : (65536 : UInt64).toNat = 65536 := rfl
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h65536, h1]
        omega
      have hp32 : ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages := by
        have hlt : st1.mem.pages < UInt32.size := by
          have hs : UInt32.size = 4294967296 := rfl
          omega
        have h1 : (UInt32.ofNat st1.mem.pages).toNat = st1.mem.pages :=
          UInt32.toNat_ofNat_of_lt' hlt
        simp [h1]
      have hng : ¬ ((UInt32.ofNat st1.mem.pages).toUInt64 <
          (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) := by
        rw [UInt64.lt_iff_toNat_lt, hp32, hpn]
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hng])]
      wp_run
      try simp only [hg0]
      try wp_run
      try simp
      have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (40 : UInt64).toNat = 40 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (32 : UInt64).toNat = 32 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (24 : UInt64).toNat = 24 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (16 : UInt64).toNat = 16 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (8 : UInt64).toNat = 8 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      rw [hsub40, hsub32, hsub24, hsub16, hsub8]
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
      simp only [hg2]
      have hcopy := copySuffix_correct env st1 ptr g0 g2 g3 bytes hLen hPtr32 hBelow
        hFit32 hg0_32 hszN_ge hszN_ge8 hlenU hadd17 hszU hraw hnot_lt8
        hFit hPages hg0 hg1 hg2 hg3 hInput hno_wrap h17 hsub1 hpn hp32 hng
        hsub40 hsub32 hsub24 hsub16 hsub8
      refine wp.conseq ?_ hcopy
      intro c hc
      cases c <;> simp_all [copyPost, copyResult, Nat.lt_succ_iff]

end Project.SharedPair.Spec
