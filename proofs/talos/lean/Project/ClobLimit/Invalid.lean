import Project.ClobLimit.ValidOrder
import Project.ClobLimit.Allocation
import Project.FixedArrayAllocation
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Invalid-order branch of `limit`

The invalid branch returns status one and the borrowed input book.  It bump
allocates one owned empty trade array when the free list is empty.  The proof
states the resulting header, counter changes, and preserved input region.
-/

namespace Project.ClobLimit.Invalid

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.Model Project.ClobLimit.ValidOrder
  Project.ClobLimit.Allocation Project.ClobPostOnly.Model
  Project.ClobPostOnly.SearchHelpers

set_option maxHeartbeats 64000000
set_option maxRecDepth 1048576

private def invalidAllocFrame (ptr : UInt64) (order : OrderL) : Locals :=
  { params := [.i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty],
    locals := [.i64 0, .i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 1, .i64 0, .i64 1, .i64 ptr, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 8, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    values := [] }

theorem limit_invalid
    (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL)
    (hlen : os.length < 4294967296)
    (hInput32 : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hBelow : ptr.toNat + (os.length * 5 + 1) * 8 ≤ g0.toNat)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hInput : OrdersAt st ptr os)
    (hInvalid : ¬validOrderL os order) :
    TerminatesWith (m := «module») (id := 21) (initial := st) (env := env)
      [.i64 order.oqty, .i64 order.oprice, .i64 order.oside,
       .i64 order.otrader, .i64 order.oid, .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (g0 + 48), .i64 ptr, .i64 1] ∧
        OrdersAt st' ptr os ∧
        FreshTradeArrayAt st' (g0 + 48) ∧
        st'.mem.pages = st.mem.pages ∧
        st'.globals.globals =
          ((st.globals.globals.set 0 (.i64 (g0 + 56))).set 2
            (.i64 (g2 + 1))) ∧
        ∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a) := by
  apply TerminatesWith.of_wp_entry_for (f := func21Def)
  · simp [«module»]
  · change wp «module» func21 _ st
      { params := [.i64 ptr, .i64 order.oid, .i64 order.otrader,
          .i64 order.oside, .i64 order.oprice, .i64 order.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func21
    wp_run
    refine wp_call_tw
      (Project.ClobLimit.ValidOrder.func6_spec env st ptr os order hlen
        hInput) ?_
    rintro st1 vs ⟨rfl, rfl⟩
    simp only [boolWord, if_neg hInvalid]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_call_tw
      (Project.ClobLimit.Allocation.func20_spec env st1) ?_
    rintro st2 vs ⟨rfl, rfl⟩
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    simp only [hg1]
    simp
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st3 s3 => st3 = st2 ∧ s3 = invalidAllocFrame ptr order)
      (μ := fun _ _ => 0)
    · exact ⟨rfl, rfl⟩
    · rintro st3 s3 ⟨rfl, rfl⟩
      simp only [invalidAllocFrame]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      simp only [hg0]
      have hnoWrap : ¬g0 + 48 + 8 < g0 := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        have h8 : (8 : UInt64).toNat = 8 := rfl
        rw [h48, h8]
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hnoWrap])]
      wp_run
      simp
      have htop : (g0 + 48 + 8).toNat = g0.toNat + 56 := by
        rw [UInt64.toNat_add, UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        have h8 : (8 : UInt64).toNat = 8 := rfl
        rw [h48, h8]
        omega
      have htopSub : (g0 + 48 + 8 - 1).toNat = g0.toNat + 55 := by
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [toNat_sub_le _ _ (by rw [h1, htop]; omega), htop]
        rw [h1]
        omega
      have hpagesNeeded :
          ((g0 + 48 + 8 - 1) / 65536 + 1).toNat =
            (g0.toNat + 55) / 65536 + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_div, htopSub]
        have h65536 : (65536 : UInt64).toNat = 65536 := rfl
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h65536, h1]
        omega
      have hmemorySize :
          ((UInt32.ofNat st3.mem.pages).toUInt64).toNat = st3.mem.pages := by
        have hlt : st3.mem.pages < UInt32.size := by
          have hs : UInt32.size = 4294967296 := rfl
          omega
        have hnat : (UInt32.ofNat st3.mem.pages).toNat = st3.mem.pages :=
          UInt32.toNat_ofNat_of_lt' hlt
        simp [hnat]
      have hnoGrow : ¬
          ((UInt32.ofNat st3.mem.pages).toUInt64 <
            (g0 + 48 + 8 - 1) / 65536 + 1) := by
        rw [UInt64.lt_iff_toNat_lt, hmemorySize, hpagesNeeded]
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hnoGrow])]
      wp_run
      simp only [hg0]
      try wp_run
      try simp
      have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48]
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
      have hnewNat : (g0 + 48).toNat = g0.toNat + 48 := by
        rw [UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48]
        omega
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
      simp only [hg2]
      refine ⟨by omega, ?_⟩
      refine ⟨by simp [func21Def], ?_, ?_, ?_, ?_⟩
      · refine OrdersAt.frame (st := st3) (st' := _) hInput32 hBelow rfl ?_
          hInput
        intro a ha
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
      · have hAlloc := emptyFixedArrayMem_spec st3 g0 8 4 hFit32
        simpa only [FreshTradeArrayAt, FreshFixedArrayAt,
          emptyFixedArrayMem, fixedArrayMem, fixedArrayHeaderMem,
          toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24,
          hsub16, hsub8, hnewNat] using hAlloc
      · have hnum : (48 : UInt64) + 8 = 56 := by decide
        rw [UInt64.add_assoc, hnum]
      · intro a ha
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

end Project.ClobLimit.Invalid
