import Project.ClobPostOnly.FindBestWrapper
import Project.ClobPostOnly.ValidOrder
import Project.ClobPostOnly.AppendOrderAlloc
import Project.ClobPostOnly.AppendOrderFinish
import Project.ClobPostOnly.AppendTrade
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Successful append branch of `postOnly`

The successful branch allocates a copied order array with the taker appended,
then allocates an empty trade array.  Its proof follows both bump allocations
and the emitted word-copy loop.  The result states exact contents, ownership,
counter changes, and the preserved input region.
-/

namespace Project.ClobPostOnly.Append

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobFindBest.Model Project.ClobPostOnly.Model
  Project.ClobPostOnly.ValidOrder Project.ClobPostOnly.FindBestWrapper
  Project.ClobPostOnly.Allocation Project.ClobPostOnly.AppendStore
  Project.ClobPostOnly.AppendTrade
  Project.ClobPostOnly.SearchHelpers

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

theorem postOnly_appended
    (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL)
    (hlen : os.length < 4294967296)
    (hInput32 : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hBelow : ptr.toNat + (os.length * 5 + 1) * 8 ≤ g0.toNat)
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hInput : OrdersAt st ptr os)
    (hValid : validOrderL os order)
    (hNoCross : findBestL os order = none) :
    TerminatesWith (m := «module») (id := 17) (initial := st) (env := env)
      [.i64 order.oqty, .i64 order.oprice, .i64 order.oside,
       .i64 order.otrader, .i64 order.oid, .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (g0 + 96 + orderArrayBytesU (os.length + 1)),
          .i64 (g0 + 48), .i64 0] ∧
        OrdersAt st' (g0 + 48) (os ++ [order]) ∧
        FreshOrderArrayAt st' (g0 + 48)
          (orderArrayBytesU (os.length + 1)) ∧
        FreshTradeArrayAt st'
          (g0 + 96 + orderArrayBytesU (os.length + 1)) ∧
        st'.mem.pages = st.mem.pages ∧
        st'.globals.globals =
          ((st.globals.globals.set 0
            (.i64 (g0 + 104 + orderArrayBytesU (os.length + 1)))).set 2
              (.i64 (g2 + 2))) ∧
        ∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a) := by
  have hlenU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have houtU : (UInt64.ofNat (os.length + 1)).toNat = os.length + 1 :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hlenAdd : UInt64.ofNat os.length + 1 =
      UInt64.ofNat (os.length + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hlenU, size_eq]; omega), hlenU, houtU]
  have htotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5 := by
    rw [UInt64.toNat_mul, hlenU]
    have h5 : (5 : UInt64).toNat = 5 := rfl
    rw [h5, Nat.mod_eq_of_lt]
    omega
  have hbytesU : (orderArrayBytesU (os.length + 1)).toNat =
      orderArrayBytes (os.length + 1) := by
    unfold orderArrayBytesU orderArrayBytes fixedArrayBytesU fixedArrayBytes
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, houtU]
    have h5 : (UInt64.ofNat 5).toNat = 5 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h5, h8]
    omega
  have htop :
      (g0 + 48 + orderArrayBytesU (os.length + 1)).toNat =
        g0.toNat + 48 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hbytesU]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hnewNat : (g0 + 48).toNat = g0.toNat + 48 := by
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hround : (orderArrayBytesU (os.length + 1) + 7) / 8 * 8 =
      orderArrayBytesU (os.length + 1) := by
    have h7 : (7 : UInt64).toNat = 7 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    have hbytesLt : orderArrayBytes (os.length + 1) + 7 < UInt64.size := by
      rw [size_eq]
      unfold orderArrayBytes fixedArrayBytes
      omega
    have hadd7 : (orderArrayBytesU (os.length + 1) + 7).toNat =
        orderArrayBytes (os.length + 1) + 7 := by
      rw [UInt64.toNat_add, hbytesU, h7, Nat.mod_eq_of_lt hbytesLt]
    have hroundedNat :
        (orderArrayBytes (os.length + 1) + 7) / 8 * 8 =
          orderArrayBytes (os.length + 1) := by
      unfold orderArrayBytes fixedArrayBytes
      omega
    have hbytesLt' : orderArrayBytes (os.length + 1) < UInt64.size := by
      omega
    apply UInt64.toNat.inj
    rw [UInt64.toNat_mul, UInt64.toNat_div, hadd7]
    change (orderArrayBytes (os.length + 1) + 7) / 8 * 8 % UInt64.size =
      (orderArrayBytesU (os.length + 1)).toNat
    rw [hroundedNat, hbytesU, Nat.mod_eq_of_lt hbytesLt']
  have hcapacity :
      (8 + (UInt64.ofNat os.length + 1) * 5 * 8 + 7) / 8 * 8 =
        orderArrayBytesU (os.length + 1) := by
    rw [hlenAdd]
    change (orderArrayBytesU (os.length + 1) + 7) / 8 * 8 = _
    exact hround
  have hcapGe : ¬ (orderArrayBytesU (os.length + 1) < (8 : UInt64)) := by
    rw [UInt64.lt_iff_toNat_lt, hbytesU]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    unfold orderArrayBytes fixedArrayBytes
    omega
  apply TerminatesWith.of_wp_entry_for (f := func17Def)
  · simp [«module»]
  · change wp «module» func17 _ st
      { params := [.i64 ptr, .i64 order.oid, .i64 order.otrader,
          .i64 order.oside, .i64 order.oprice, .i64 order.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func17
    wp_run
    refine wp_call_tw
      (Project.ClobPostOnly.ValidOrder.func6_spec env st ptr os order hlen
        hInput) ?_
    rintro st1 vs ⟨rfl, rfl⟩
    simp only [boolWord, if_pos hValid]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_call_tw
      (Project.ClobPostOnly.FindBestWrapper.func13_spec env st1 ptr os order
        hlen hInput) ?_
    rintro st2 vs ⟨hvs, rfl⟩
    simp [optionVals, hNoCross] at hvs
    subst vs
    simp only [optionPayload, optionTag]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_call_tw
      (Project.ClobPostOnly.Allocation.func15_spec env st2) ?_
    rintro st3 vs ⟨rfl, rfl⟩
    wp_run
    simp
    rw [hInput.1.1]
    refine ⟨hInput.1.2, ?_⟩
    refine wp_iff_cons rfl ?_
    simp [hcapacity, hcapGe]
    try simp only [hg1]
    try wp_run
    change wp «module»
      (AppendOrderAlloc.appendOrderAllocProg ++
        AppendOrderCopy.appendOrderCopyProg ++
        AppendOrderFinish.appendOrderFinishProg ++
        AppendTrade.appendTradeProg) _ st3
      (AppendOrderAlloc.appendAllocFrame ptr order os.length) env
    refine AppendOrderAlloc.appendOrderAllocProg_spec env st3 ptr g0 g2 os
      order hlenAdd hbytesU htop hFit32 hFit hPages hg0 hg2 _ _ ?_
    intro st4 hCopyInit
    refine AppendOrderCopy.appendOrderCopyProg_spec env st3 st4 ptr g0 g2 os
      order hInput32 hBelow htotalU hnewNat hFit32 hFit _ _ hCopyInit ?_
    intro st5 hCopyDone
    refine AppendOrderFinish.appendOrderFinishProg_spec env st3 st5 ptr g0 g2
      os order hnewNat hFit32 hFit hg0 hg1 hg2 hInput _ _ hCopyDone ?_
    intro st6 hFinish
    obtain ⟨hBook, hFresh, hPageFrame, hGlobalFrame, hLowFrame, hg0_6,
      hg1_6, hg2_6⟩ := hFinish
    have hFit6 :
        g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
          st6.mem.pages * 65536 := by
      rw [hPageFrame]
      exact hFit
    have hPages6 : st6.mem.pages ≤ 65536 := by
      rw [hPageFrame]
      exact hPages
    have hTrade := AppendTrade.appendTradeProg_spec env st3 st6 ptr g0 g2 os
      order
      hnewNat hbytesU htop hFit32 hFit6 hPages6 hg0_6 hg1_6 hg2_6 hBook
      hFresh hPageFrame hGlobalFrame hLowFrame
    refine wp.imp hTrade ?_
    intro c hc
    cases c with
    | Fallthrough st' s' =>
        simp only [AppendTrade.appendTradeAssertion,
          AppendTradeStore.appendTradeAssertion] at hc
        rcases hc with ⟨h31, h32, h33, hPost⟩
        simp only [Locals.get] at h31 h32 h33
        simp only [h31, h32, h33]
        simpa only [AppendTrade.appendTradePost,
          AppendTradeStore.appendTradePost, func17Def, List.length, List.take,
          List.drop, List.nil_append, List.append_nil] using hPost
    | _ =>
        simp only [AppendTrade.appendTradeAssertion,
          AppendTradeStore.appendTradeAssertion] at hc

end Project.ClobPostOnly.Append
