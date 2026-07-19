import Project.PushTwice.Base

/-!
# The `pushBangSize` helper on the reuse path

The free list holds one node of exactly the needed capacity, so the
allocation unlinks it instead of extending the heap.
-/

namespace Project.PushTwice.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

/-- Copy-loop invariant for the reuse path: identical to `vInv` except the
allocator state is the post-unlink state, with the heap top untouched and
the free list emptied. -/
def vInvR (st0 : Store Unit) (ptr g0 g2 : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ bytes.length ∧
      s = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 0 ptr (UInt64.ofNat bytes.length) 33
        (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k)
        (allocSizeU (UInt64.ofNat bytes.length)) 0 (g0 + 48)
        (allocSizeU (UInt64.ofNat bytes.length)) 0
        (g0 + 48) ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        ((st0.globals.globals.set 1 (.i64 0)).set 2 (.i64 (g2 + 1))) ∧
      (∀ a : Nat, a < g0.toNat → st.mem.bytes a = st0.mem.bytes a) ∧
      (∀ i : Nat, i < k → st.mem.bytes (g0.toNat + 48 + i) = bytes[i]!) ∧
      st.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
        5501223100278326855 ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
        allocSizeU (UInt64.ofNat bytes.length) ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0

def rMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: .i64 l19 :: _ =>
      if l19 = 0 then 1 else 0
  | _ => 0

/-- The helper on a free list holding one node of exactly the needed
capacity: the allocation unlinks the node instead of extending the heap, so
the heap top is unchanged, and the released temporary restores the node to
the free-list head. -/
theorem func0_reuse
    (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 g4 g5 : UInt64)
    (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 48 + allocSize (bytes.length + 1) < 4294967296)
    (hFit : g0.toNat + 48 + allocSize (bytes.length + 1) ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? =
      some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))))
    (hg1 : st.globals.globals[1]? = some (.i64 (g0 + 48)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (hcap : st.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
      allocSizeU (UInt64.ofNat bytes.length))
    (hnext : st.mem.read64 (UInt32.ofNat ((g0.toNat + 40) % 4294967296)) = 0)
    (hInput : BytesAt st ptr bytes) :
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr, .i64 0]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat bytes.length + 1)] ∧
        st'.mem.pages = st.mem.pages ∧
        st'.globals.globals[0]? =
          some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) ∧
        st'.globals.globals[1]? = some (.i64 (g0 + 48)) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1)) ∧
        st'.globals.globals[3]? = st.globals.globals[3]? ∧
        st'.globals.globals[4]? = some (.i64 (g4 + 1)) ∧
        st'.globals.globals[5]? = some (.i64 (g5 + 1)) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 0 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
          allocSizeU (UInt64.ofNat bytes.length) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 40) % 4294967296)) = 0 ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a)) := by
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
  have hgp : (g0 + 48 : UInt64).toNat = g0.toNat + 48 := by
    rw [UInt64.toNat_add]
    have hc : (48 : UInt64).toNat = 48 := rfl
    rw [hc]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
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
  have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
    rw [UInt64.toNat_sub, UInt64.toNat_add]
    have ha : (48 : UInt64).toNat = 48 := rfl
    rw [ha]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hnode0 : ¬ ((g0 + 48 : UInt64) = 0) := by
    intro h
    have := congrArg UInt64.toNat h
    rw [hgp] at this
    simp at this
  have hcap' : st.mem.read64 ((g0 + 48 - 32).toUInt32) =
      allocSizeU (UInt64.ofNat bytes.length) := by
    rw [toUInt32_eq_ofNat, hsub32]
    exact hcap
  have hnext' : st.mem.read64 ((g0 + 48 - 8).toUInt32) = 0 := by
    rw [toUInt32_eq_ofNat, hsub8]
    exact hnext
  have hraw : ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8).toNat =
      allocSize (bytes.length + 1) := hszU
  have hnot_lt8 :
      ¬ ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8 < (8 : UInt64)) := by
    rw [UInt64.lt_iff_toNat_lt, hraw]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    omega
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 0, .i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0],
        values := [] } env
    unfold func0
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnot_lt8])]
    wp_run
    try simp only [hg1]
    try wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st1 s1 =>
        (st1 = st ∧
          s1 = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
            (UInt64.ofNat bytes.length) 0 0 ptr (UInt64.ofNat bytes.length) 33
            0 (UInt64.ofNat bytes.length + 1) 0
            (allocSizeU (UInt64.ofNat bytes.length)) 0 (g0 + 48) 0 0 0) ∨
        (s1 = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
            (UInt64.ofNat bytes.length) 0 0 ptr (UInt64.ofNat bytes.length) 33
            0 (UInt64.ofNat bytes.length + 1) 0
            (allocSizeU (UInt64.ofNat bytes.length)) 0 (g0 + 48)
            (allocSizeU (UInt64.ofNat bytes.length)) 0 (g0 + 48) ∧
          st1.mem.pages = st.mem.pages ∧
          st1.globals.globals = st.globals.globals.set 1 (.i64 0) ∧
          (∀ a : Nat, a < g0.toNat → st1.mem.bytes a = st.mem.bytes a) ∧
          st1.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
            5501223100278326855 ∧
          st1.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 ∧
          st1.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
            allocSizeU (UInt64.ofNat bytes.length) ∧
          st1.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0))
      (μ := rMeasure)
    · exact Or.inl ⟨rfl, by simp [vFrame, allocSizeU]⟩
    · rintro st1 s1 (⟨rfl, rfl⟩ | ⟨rfl, hpg, hgl, hlo, hh0, hh8, hh16, hh24⟩)
      · -- first iteration: the head has the needed capacity, take it
        simp only [vFrame]
        wp_run
        try simp
        rw [if_neg hnode0]
        try simp
        refine ⟨by omega, by omega, ?_⟩
        have hcapS : st1.mem.read64
            (UInt32.ofNat ((g0 + 48 - 32).toNat % 4294967296)) =
            allocSizeU (UInt64.ofNat bytes.length) := by
          rw [hsub32]
          exact hcap
        have hnextS : st1.mem.read64
            (UInt32.ofNat ((g0 + 48 - 8).toNat % 4294967296)) = 0 := by
          rw [hsub8]
          exact hnext
        try simp only [hcapS, hnextS]
        try wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by decide)]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        try simp
        try simp only [hg1]
        try simp
        rw [hsub40, hsub32, hsub24, hsub16, hsub8]
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        refine ⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩, by simp [rMeasure, hnode0]⟩
        · intro a ha
          rw [write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
        · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
        · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
        · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
        · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
      · -- second iteration: the result local is set, exit the walk
        simp only [vFrame]
        wp_run
        try simp
        rw [if_neg hnode0]
        try simp
        rw [if_neg hnode0]
        try simp
        try wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        have hglenB : 5 < st.globals.globals.length := by
          obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hg5
          exact h
        have hg2S : st1.globals.globals[2]? = some (.i64 g2) := by
          rw [hgl]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (1 = 2))]
          exact hg2
        wp_run
        try simp only [hg2S]
        try wp_run
        try simp
        apply wp_block_cons
        apply wp_loop_cons (Inv := vInvR st ptr g0 g2 bytes) (μ := vMeasure bytes)
        · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [vFrame]
          · exact hpg
          · rw [hgl]
          · exact hlo
          · intro i hi
            omega
          · exact hh0
          · exact hh8
          · exact hh16
          · exact hh24
        · rintro st2 s2 ⟨k, hk, rfl, hpg2, hgl2, hlo2, hpref, hp0f, hp8f, hp16f, hp24f⟩
          have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
          simp only [vFrame]
          wp_run
          try simp
          by_cases hkend : k = bytes.length
          · -- all bytes copied: exit, store the bang, release, return
            have hle : (UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k) := by
              rw [UInt64.le_iff_toNat_le, hkU, hlenU]
              omega
            have hge : UInt64.ofNat k ≥ UInt64.ofNat bytes.length := hle
            rw [if_pos hge]
            try simp
            subst hkend
            have hgp : (g0 + 48 : UInt64).toNat = g0.toNat + 48 := by
              rw [UInt64.toNat_add]
              have hc : (48 : UInt64).toNat = 48 := rfl
              rw [hc]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hb0 : ((g0 + 48 - 48 : UInt64)).toUInt32 =
                UInt32.ofNat (g0.toNat % 4294967296) := by
              rw [toUInt32_eq_ofNat, hsub48]
            have hb40 : ((g0 + 48 - 40 : UInt64)).toUInt32 =
                UInt32.ofNat ((g0.toNat + 8) % 4294967296) := by
              rw [toUInt32_eq_ofNat, hsub40]
            have hb24 : ((g0 + 48 - 24 : UInt64)).toUInt32 =
                UInt32.ofNat ((g0.toNat + 24) % 4294967296) := by
              rw [toUInt32_eq_ofNat, hsub24]
            have hb8 : ((g0 + 48 - 8 : UInt64)).toUInt32 =
                UInt32.ofNat ((g0.toNat + 40) % 4294967296) := by
              rw [toUInt32_eq_ofNat, hsub8]
            have hglen : 5 < st.globals.globals.length := by
              obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hg5
              exact h
            have hg0len : 0 < st.globals.globals.length := by omega
            have hg1len : 1 < st.globals.globals.length := by omega
            have hg2len : 2 < st.globals.globals.length := by omega
            have hg4len : 4 < st.globals.globals.length := by omega
            have hgnil : ¬ st.globals.globals = [] := by
              intro h
              rw [h] at hglen
              simp at hglen
            refine ⟨by omega, ?_⟩
            refine wp_call_tw (func5_frees_fresh_raw env _ (g0 + 48) 0 g4 g5
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
            · rw [hgp]
              omega
            · rw [hgp]
              omega
            · dsimp only
              rw [write8_pages, hpg2]
              omega
            · dsimp only
              rw [hb0, read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp0f
            · dsimp only
              rw [hb40, read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp8f
            · dsimp only
              rw [hb24, read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp24f
            · dsimp only
              rw [hgl2]
              simp [hg1len]
            · dsimp only
              rw [hgl2]
              simp [hg4len]
              exact (List.getElem?_eq_some_iff.mp hg4).choose_spec
            · dsimp only
              rw [hgl2]
              simp [hglen]
              exact (List.getElem?_eq_some_iff.mp hg5).choose_spec
            rintro st3 vs ⟨rfl, hmem3, hgl3⟩
            rw [hb40, hb8] at hmem3
            dsimp only at hgl3
            rw [hgl2] at hgl3
            wp_run
            try simp
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [func0Def]
            · rw [hmem3]
              rw [Mem.write64_pages, Mem.write64_pages, write8_pages, hpg2]
            · rw [hgl3]
              simp [hg0len]
              exact (List.getElem?_eq_some_iff.mp hg0).choose_spec
            · rw [hgl3]
              simp [hg1len]
            · rw [hgl3]
              simp [hg2len]
            · rw [hgl3]
              simp
            · rw [hgl3]
              simp [hg4len]
            · rw [hgl3]
              simp [hglen]
            · rw [hmem3]
              rw [read64_write64_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                Mem.read64_write64_same]
            · rw [hmem3]
              rw [read64_write64_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _
                  (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write8_ne _ _ _ _
                  (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp16f
            · rw [hmem3]
              rw [Mem.read64_write64_same]
            · intro a ha
              rw [hmem3]
              rw [write64_bytes_ne _ _ _
                  (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_ne _ _ _
                  (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write8_bytes_ne _ _ _
                  (by rw [toUInt32_ofNat_mod_toNat]; omega)]
              exact hlo2 a ha
          · -- copy one byte and continue
            have hklt : k < bytes.length := Nat.lt_of_le_of_ne hk hkend
            have hnotle : ¬ ((UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k)) := by
              rw [UInt64.le_iff_toNat_le, hkU, hlenU]
              omega
            have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat bytes.length) := hnotle
            rw [if_neg hnge]
            try simp
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
              rw [hlo2 (ptr.toNat + k) (by omega)]
              have hthis := hread
              rw [Mem.read8, toUInt32_ofNat_mod_toNat,
                Nat.mod_eq_of_lt (by omega)] at hthis
              exact hthis
            rw [hreadval]
            refine ⟨by omega, by omega,
              ⟨k + 1, hklt, ?_, hpg2, hgl2, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
            · rw [← hkadd]
              simp only [vFrame]
            · intro a ha
              rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
              exact hlo2 a ha
            · intro i hi
              by_cases hieq : i = k
              · subst hieq
                rw [write8_bytes_hit _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
              · rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
                exact hpref i (by omega)
            · rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp0f
            · rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp8f
            · rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp16f
            · rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hp24f
            · simp [vMeasure]
              omega


end Project.PushTwice.Spec
