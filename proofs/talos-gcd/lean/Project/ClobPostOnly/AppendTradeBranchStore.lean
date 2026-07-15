import Project.ClobPostOnly.AppendTradeStore

/-!
# Trade-array stores in an `iff` branch

The bump allocator writes the trade-array header inside an `iff`, then performs
the length write and result loads after the branch.  This module states the
exact continuation produced by the zero-arity `iff` rule.  The address and page
checks can apply the compiled result without elaborating the stores again.
-/

namespace Project.ClobPostOnly.AppendTradeBranchStore

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def appendTradeCheckedFrame (ptr g0 : UInt64) (order : OrderL)
    (n : Nat) : Locals :=
  { AppendTradeStore.appendTradeStoreFrame ptr g0 order n with values := [] }

def appendTradeBranchHeaderProg : Wasm.Program :=
  .globalGet 0 :: AppendTradeStore.appendTradeStoreHeaderProg

def appendTradeBranchContinuation (env : HostEnv Unit) (st0 : Store Unit)
    (g0 g2 : UInt64) (os : List OrderL) (order : OrderL) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp «module» AppendTradeStore.appendTradeStoreTailProg
          (AppendTradeStore.appendTradeAssertion st0 g0 g2 os order) st'
          { s' with values := [] } env
    | .Break 0 st' s' =>
        wp «module» AppendTradeStore.appendTradeStoreTailProg
          (AppendTradeStore.appendTradeAssertion st0 g0 g2 os order) st'
          { s' with values := [] } env
    | .Break (k + 1) st' s' =>
        AppendTradeStore.appendTradeAssertion st0 g0 g2 os order
          (.Break k st' s')
    | other => AppendTradeStore.appendTradeAssertion st0 g0 g2 os order other

set_option Elab.async false in
theorem appendTradeBranchHeaderProg_spec (env : HostEnv Unit)
    (st0 st6 : Store Unit) (ptr g0 g2 : UInt64) (os : List OrderL)
    (order : OrderL)
    (hnewNat : (g0 + 48).toNat = g0.toNat + 48)
    (hbytesU : (orderArrayBytesU (os.length + 1)).toNat =
      orderArrayBytes (os.length + 1))
    (htop : (g0 + 48 + orderArrayBytesU (os.length + 1)).toNat =
      g0.toNat + 48 + orderArrayBytes (os.length + 1))
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st6.mem.pages * 65536)
    (hg0 : st6.globals.globals[0]? = some
      (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1))))
    (hg2 : st6.globals.globals[2]? = some (.i64 (g2 + 1)))
    (hBook : OrdersAt st6 (g0 + 48) (os ++ [order]))
    (hFresh : FreshOrderArrayAt st6 (g0 + 48)
      (orderArrayBytesU (os.length + 1)))
    (hPageFrame : st6.mem.pages = st0.mem.pages)
    (hGlobalFrame : st6.globals.globals =
      ((st0.globals.globals.set 0
        (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1)))).set 2
          (.i64 (g2 + 1))))
    (hLowFrame : ∀ a : Nat, a < g0.toNat →
      st6.mem.bytes a = st0.mem.bytes a) :
    wp «module» appendTradeBranchHeaderProg
      (appendTradeBranchContinuation env st0 g0 g2 os order) st6
      (appendTradeCheckedFrame ptr g0 order os.length) env := by
  unfold appendTradeBranchContinuation
  unfold AppendTradeStore.appendTradeAssertion
  simp only [appendTradeBranchHeaderProg, appendTradeCheckedFrame,
    AppendTradeStore.appendTradeStoreHeaderProg,
    AppendTradeStore.appendTradeStoreTailProg,
    AppendTradeStore.appendTradeStoreFrame]
  wp_run
  simp only [hg0]
  try simp
  simp only [hbytesU]
  have htradeNat :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48).toNat =
        g0.toNat + 96 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_add, htop]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hbase8 :
      g0.toNat + 48 + orderArrayBytes (os.length + 1) + 8 =
        g0.toNat + 56 + orderArrayBytes (os.length + 1) := by omega
  have hbase16 :
      g0.toNat + 48 + orderArrayBytes (os.length + 1) + 16 =
        g0.toNat + 64 + orderArrayBytes (os.length + 1) := by omega
  have hbase24 :
      g0.toNat + 48 + orderArrayBytes (os.length + 1) + 24 =
        g0.toNat + 72 + orderArrayBytes (os.length + 1) := by omega
  have hbase32 :
      g0.toNat + 48 + orderArrayBytes (os.length + 1) + 32 =
        g0.toNat + 80 + orderArrayBytes (os.length + 1) := by omega
  have hbase40 :
      g0.toNat + 48 + orderArrayBytes (os.length + 1) + 40 =
        g0.toNat + 88 + orderArrayBytes (os.length + 1) := by omega
  have hbase48 :
      g0.toNat + 48 + orderArrayBytes (os.length + 1) + 48 =
        g0.toNat + 96 + orderArrayBytes (os.length + 1) := by omega
  have htSub48 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 - 48).toNat =
        g0.toNat + 48 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_sub, htradeNat]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have htSub40 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 - 40).toNat =
        g0.toNat + 56 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_sub, htradeNat]
    have h40 : (40 : UInt64).toNat = 40 := rfl
    rw [h40]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have htSub32 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 - 32).toNat =
        g0.toNat + 64 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_sub, htradeNat]
    have h32 : (32 : UInt64).toNat = 32 := rfl
    rw [h32]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have htSub24 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 - 24).toNat =
        g0.toNat + 72 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_sub, htradeNat]
    have h24 : (24 : UInt64).toNat = 24 := rfl
    rw [h24]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have htSub16 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 - 16).toNat =
        g0.toNat + 80 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_sub, htradeNat]
    have h16 : (16 : UInt64).toNat = 16 := rfl
    rw [h16]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have htSub8 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 - 8).toNat =
        g0.toNat + 88 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_sub, htradeNat]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have htradePtr :
      (g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 =
        g0 + 96 + orderArrayBytesU (os.length + 1) := by
    have h96 : (96 : UInt64) = 48 + 48 := by decide
    rw [h96]
    ac_rfl
  have hfinalPtr :
      (g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 + 8 =
        g0 + 104 + orderArrayBytesU (os.length + 1) := by
    have h104 : (104 : UInt64) = 48 + 48 + 8 := by decide
    rw [h104]
    ac_rfl
  have hg2Next : g2 + 1 + 1 = g2 + 2 := by
    have h2 : (2 : UInt64) = 1 + 1 := by decide
    rw [h2]
    ac_rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  simp only [hg2]
  refine ⟨by omega, ?_⟩
  refine ⟨by simp [func17Def, htradePtr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine OrdersAt.frame (st := st6) (st' := _)
        (by
          simp only [List.length_append, List.length_singleton, hnewNat]
          unfold orderArrayBytes fixedArrayBytes at hFit32
          omega)
        (by
          simp only [List.length_append, List.length_singleton, hnewNat]
          rw [htop]
          unfold orderArrayBytes fixedArrayBytes
          omega)
        rfl ?_ hBook
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
  · refine FreshFixedArrayAt.frame (st := st6) (st' := _)
        (base := g0 + 48 + orderArrayBytesU (os.length + 1))
        (by rw [hnewNat]; omega) (by rw [hnewNat]; omega)
        (by rw [hnewNat, htop]; omega) ?_ hFresh
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
  · rw [← htradePtr]
    have hAlloc := emptyFixedArrayMem_spec st6
      (g0 + 48 + orderArrayBytesU (os.length + 1)) 8 4 (by
        rw [htop]
        omega)
    simpa only [FreshTradeArrayAt, FreshFixedArrayAt, emptyFixedArrayMem,
      toUInt32_eq_ofNat, htSub48, htSub40, htSub32, htSub24, htSub16,
      htSub8, htradeNat, htop, hbase8, hbase16, hbase24, hbase32,
      hbase40, hbase48] using hAlloc
  · exact hPageFrame
  · rw [hGlobalFrame]
    rw [List.set_comm _ _ (by decide : 2 ≠ 0)]
    simp only [List.set_set]
    simp [hfinalPtr, hg2Next]
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
    exact hLowFrame a ha

end Project.ClobPostOnly.AppendTradeBranchStore
