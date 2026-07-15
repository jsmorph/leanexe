import Project.ClobPostOnly.AppendOrderCopy
import Project.ClobPostOnly.AppendStore
import Project.ClobPostOnly.AppendTrade

/-!
# Appended order-array finalization

The successful `postOnly` branch stores the appended order after copying the
old order words.  It then prepares the empty trade-array allocator locals.  This
module proves that generated instruction slice and reconstructs the completed
order array before passing control to an opaque rest program.
-/

namespace Project.ClobPostOnly.AppendOrderFinish

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation Project.ClobPostOnly.AppendOrderCopy
  Project.ClobPostOnly.AppendStore

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_big" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

def appendOrderFinishProg : Wasm.Program :=
  [
  .localGet 38,
  .localGet 35,
  .constI64 (5 : UInt64),
  .mulI64,
  .constI64 (1 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 40,
  .store64 (0 : UInt32),
  .localGet 38,
  .localGet 35,
  .constI64 (5 : UInt64),
  .mulI64,
  .constI64 (2 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 41,
  .store64 (0 : UInt32),
  .localGet 38,
  .localGet 35,
  .constI64 (5 : UInt64),
  .mulI64,
  .constI64 (3 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 42,
  .store64 (0 : UInt32),
  .localGet 38,
  .localGet 35,
  .constI64 (5 : UInt64),
  .mulI64,
  .constI64 (4 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 43,
  .store64 (0 : UInt32),
  .localGet 38,
  .localGet 35,
  .constI64 (5 : UInt64),
  .mulI64,
  .constI64 (5 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 44,
  .store64 (0 : UInt32),
  .localGet 38,
  .localSet 25,
  .localGet 25,
  .localSet 32,
  .constI64 (8 : UInt64),
  .constI64 (0 : UInt64),
  .constI64 (4 : UInt64),
  .mulI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .constI64 (7 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .divUI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .localSet 41,
  .localGet 41,
  .constI64 (8 : UInt64),
  .ltUI64,
  .iff 0 0 [
    .constI64 (8 : UInt64),
    .localSet 41
  ] [],
  .constI64 (0 : UInt64),
  .localSet 46,
  .constI64 (0 : UInt64),
  .localSet 42,
  .globalGet 1,
  .localSet 43
]

def appendOrderFinishPost (st0 st6 : Store Unit) (g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL) : Prop :=
  OrdersAt st6 (g0 + 48) (os ++ [order]) ∧
    FreshOrderArrayAt st6 (g0 + 48)
      (orderArrayBytesU (os.length + 1)) ∧
    st6.mem.pages = st0.mem.pages ∧
    st6.globals.globals =
      ((st0.globals.globals.set 0
        (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1)))).set 2
          (.i64 (g2 + 1))) ∧
    (∀ a : Nat, a < g0.toNat → st6.mem.bytes a = st0.mem.bytes a) ∧
    st6.globals.globals[0]? = some
      (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1))) ∧
    st6.globals.globals[1]? = some (.i64 0) ∧
    st6.globals.globals[2]? = some (.i64 (g2 + 1))

set_option Elab.async false in
theorem appendOrderFinishProg_spec (env : HostEnv Unit)
    (st0 st5 : Store Unit) (ptr g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL)
    (hnewNat : (g0 + 48).toNat = g0.toNat + 48)
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st0.mem.pages * 65536)
    (hg0 : st0.globals.globals[0]? = some (.i64 g0))
    (hg1 : st0.globals.globals[1]? = some (.i64 0))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (hInput : OrdersAt st0 ptr os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hInv : appendCopyInv st0 ptr g0 g2 os order (os.length * 5) st5
      (appendCopyFrame ptr g0 order os.length (os.length * 5)))
    (hNext : ∀ st6,
      appendOrderFinishPost st0 st6 g0 g2 os order →
      wp «module» rest Q st6
        (AppendTrade.appendTradeAllocFrame ptr g0 order os.length) env) :
    wp «module» (appendOrderFinishProg ++ rest) Q st5
      (appendCopyFrame ptr g0 order os.length (os.length * 5)) env := by
  obtain ⟨k, hk, hFrame, hpg, hgl, hfresh, hlength, hlo, hcopied⟩ := hInv
  have hkU : UInt64.ofNat (os.length * 5) = UInt64.ofNat k := by
    have h := congrArg (fun s : Locals => s.locals[33]?) hFrame
    simpa [appendCopyFrame] using h
  have hkEq : k = os.length * 5 := by
    have h := congrArg UInt64.toNat hkU
    rw [toNat_ofNat_lt (by
        rw [size_eq]
        unfold orderArrayBytes fixedArrayBytes at hFit32
        omega),
      toNat_ofNat_lt (by
        rw [size_eq]
        unfold orderArrayBytes fixedArrayBytes at hFit32
        omega)] at h
    omega
  subst k
  have htotalEq : UInt64.ofNat (os.length * 5) =
      UInt64.ofNat os.length * 5 := by
    apply UInt64.toNat.inj
    rw [toNat_ofNat_lt (by
        rw [size_eq]
        unfold orderArrayBytes fixedArrayBytes at hFit32
        omega),
      UInt64.toNat_mul,
      toNat_ofNat_lt (by
        rw [size_eq]
        unfold orderArrayBytes fixedArrayBytes at hFit32
        omega)]
    have h5 : (5 : UInt64).toNat = 5 := rfl
    rw [h5, Nat.mod_eq_of_lt (by
      unfold orderArrayBytes fixedArrayBytes at hFit32
      omega)]
  simp only [appendOrderFinishProg, appendCopyFrame, List.cons_append,
    List.nil_append]
  wp_run_big
  try simp
  have hwriteAddr (r : Nat) (hr1 : 1 ≤ r) (hr5 : r ≤ 5) :
      g0.toNat + 48 + (os.length * 5 + r) * 8 < 4294967296 := by
    unfold orderArrayBytes fixedArrayBytes at hFit32
    omega
  have hwriteBound (r : Nat) (hr1 : 1 ≤ r) (hr5 : r ≤ 5) :
      (g0.toNat + 48 + (os.length * 5 + r) * 8) % 4294967296 + 8 ≤
        st5.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (hwriteAddr r hr1 hr5), hpg]
    have hFit' := hFit
    unfold orderArrayBytes fixedArrayBytes at hFit'
    omega
  rw [if_neg (Nat.not_lt.mpr (hwriteBound 1 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hwriteBound 2 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hwriteBound 3 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hwriteBound 4 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hwriteBound 5 (by omega) (by omega)))]
  let st6 := appendOrderStore st5 g0 os.length order
  have hpg6 : st6.mem.pages = st0.mem.pages := by
    simp only [st6, appendOrderStore, Mem.write64_pages, hpg]
  have hgl6 : st6.globals.globals =
      ((st0.globals.globals.set 0
        (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1)))).set 2
          (.i64 (g2 + 1))) := by
    exact hgl
  have hg1_5 : st5.globals.globals[1]? = some (.i64 0) := by
    rw [hgl]
    simp [(List.getElem?_eq_some_iff.mp hg1).choose]
    exact (List.getElem?_eq_some_iff.mp hg1).choose_spec
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
  have hlo6 : ∀ a : Nat, a < g0.toNat →
      st6.mem.bytes a = st0.mem.bytes a := by
    intro a ha
    simp only [st6, appendOrderStore]
    rw [write64_bytes_lo _ _ _
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (hwriteAddr 5 (by omega) (by omega))]
            omega),
      write64_bytes_lo _ _ _
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (hwriteAddr 4 (by omega) (by omega))]
            omega),
      write64_bytes_lo _ _ _
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (hwriteAddr 3 (by omega) (by omega))]
            omega),
      write64_bytes_lo _ _ _
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (hwriteAddr 2 (by omega) (by omega))]
            omega),
      write64_bytes_lo _ _ _
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (hwriteAddr 1 (by omega) (by omega))]
            omega)]
    exact hlo a ha
  have hfresh6 : FreshOrderArrayAt st6 (g0 + 48)
      (orderArrayBytesU (os.length + 1)) := by
    obtain ⟨hh0, hh8, hh16, hh24, hh32, hh40⟩ := hfresh
    unfold FreshOrderArrayAt FreshFixedArrayAt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        _ = st5.mem.read64 ((g0 + 48 - 48).toUInt32) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order _ (hwriteAddr 5 (by omega) (by omega))
            (by simp only [toUInt32_eq_ofNat, hsub48,
              toUInt32_ofNat_mod_toNat]; omega)
        _ = _ := hh0
    · calc
        _ = st5.mem.read64 ((g0 + 48 - 40).toUInt32) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order _ (hwriteAddr 5 (by omega) (by omega))
            (by simp only [toUInt32_eq_ofNat, hsub40,
              toUInt32_ofNat_mod_toNat]; omega)
        _ = _ := hh8
    · calc
        _ = st5.mem.read64 ((g0 + 48 - 32).toUInt32) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order _ (hwriteAddr 5 (by omega) (by omega))
            (by simp only [toUInt32_eq_ofNat, hsub32,
              toUInt32_ofNat_mod_toNat]; omega)
        _ = _ := hh16
    · calc
        _ = st5.mem.read64 ((g0 + 48 - 24).toUInt32) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order _ (hwriteAddr 5 (by omega) (by omega))
            (by simp only [toUInt32_eq_ofNat, hsub24,
              toUInt32_ofNat_mod_toNat]; omega)
        _ = _ := hh24
    · calc
        _ = st5.mem.read64 ((g0 + 48 - 16).toUInt32) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order _ (hwriteAddr 5 (by omega) (by omega))
            (by simp only [toUInt32_eq_ofNat, hsub16,
              toUInt32_ofNat_mod_toNat]; omega)
        _ = _ := hh32
    · calc
        _ = st5.mem.read64 ((g0 + 48 - 8).toUInt32) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order _ (hwriteAddr 5 (by omega) (by omega))
            (by simp only [toUInt32_eq_ofNat, hsub8,
              toUInt32_ofNat_mod_toNat]; omega)
        _ = _ := hh40
  have houtBound (j field : Nat) (hj : j < os.length + 1)
      (hfield : field < 5) :
      ((g0 + 48).toNat + (j * 5 + field + 1) * 8) % 4294967296 + 8 ≤
        st6.mem.pages * 65536 := by
    rw [hnewNat, Nat.mod_eq_of_lt (by
      unfold orderArrayBytes fixedArrayBytes at hFit32
      omega), hpg6]
    have hFit' := hFit
    unfold orderArrayBytes fixedArrayBytes at hFit'
    omega
  have hBook : OrdersAt st6 (g0 + 48) (os ++ [order]) := by
    apply OrdersAt.ofFlatWords
    · calc
        _ = st5.mem.read64
            (UInt32.ofNat ((g0 + 48).toNat % 4294967296)) := by
          simpa only [st6] using appendOrderStore_read_before st5 g0
            os.length order
            (UInt32.ofNat ((g0 + 48).toNat % 4294967296))
            (hwriteAddr 5 (by omega) (by omega))
            (by
              rw [toUInt32_ofNat_mod_toNat, hnewNat,
                Nat.mod_eq_of_lt (by
                  unfold orderArrayBytes fixedArrayBytes at hFit32
                  omega)]
              omega)
        _ = _ := by
          rw [← toUInt32_eq_ofNat]
          simpa using hlength
    · rw [hnewNat, Nat.mod_eq_of_lt (by
        unfold orderArrayBytes fixedArrayBytes at hFit32
        omega), hpg6]
      have hFit' := hFit
      unfold orderArrayBytes fixedArrayBytes at hFit'
      omega
    · intro j hj field hfield
      by_cases hjOld : j < os.length
      · have hget : (os ++ [order])[j]! = os[j]! := by
          rw [getBang_eq hj, getBang_eq hjOld]
          exact List.getElem_append_left hjOld
        rw [hget]
        calc
          orderWord st6 (g0 + 48) (j * 5 + field) =
              orderWord st5 (g0 + 48) (j * 5 + field) := by
            unfold orderWord
            simpa only [st6] using appendOrderStore_read_before st5 g0
              os.length order _ (hwriteAddr 5 (by omega) (by omega))
              (by
                rw [toUInt32_ofNat_mod_toNat, hnewNat,
                  Nat.mod_eq_of_lt (by
                    unfold orderArrayBytes fixedArrayBytes at hFit32
                    omega)]
                omega)
          _ = orderWord st0 ptr (j * 5 + field) := hcopied _ (by omega)
          _ = os[j]!.word field := hInput.orderWord_eq j field hjOld hfield
      · have hjEq : j = os.length := by
          simp at hj
          omega
        subst j
        have hget : (os ++ [order])[os.length]! = order := by
          simp [getElem!_pos]
        rw [hget]
        obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ :=
          appendOrderStore_reads st5 g0 os.length order
            (hwriteAddr 5 (by omega) (by omega))
        unfold orderWord
        interval_cases field
        · simpa only [st6, hnewNat, OrderL.word] using hr1
        · simpa only [st6, hnewNat, OrderL.word] using hr2
        · simpa only [st6, hnewNat, OrderL.word] using hr3
        · simpa only [st6, hnewNat, OrderL.word] using hr4
        · simpa only [st6, hnewNat, OrderL.word] using hr5
    · intro j hj field hfield
      apply houtBound j field
      · simpa using hj
      · exact hfield
  have hg0_6 : st6.globals.globals[0]? = some
      (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1))) := by
    rw [hgl6]
    simp [(List.getElem?_eq_some_iff.mp hg0).choose]
  have hg1_6 : st6.globals.globals[1]? = some (.i64 0) := by
    rw [hgl6]
    simp [(List.getElem?_eq_some_iff.mp hg1).choose]
    exact (List.getElem?_eq_some_iff.mp hg1).choose_spec
  have hg2_6 : st6.globals.globals[2]? = some (.i64 (g2 + 1)) := by
    rw [hgl6]
    simp [(List.getElem?_eq_some_iff.mp hg2).choose]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  simp only [hg1_5]
  simp
  have hRest := hNext st6
    ⟨hBook, hfresh6, hpg6, hgl6, hlo6, hg0_6, hg1_6, hg2_6⟩
  simpa only [st6, appendOrderStore, AppendTrade.appendTradeAllocFrame,
    AppendTradeBump.appendTradeAllocFrame,
    AppendTradeBumpChecks.appendTradeAllocFrame, htotalEq] using hRest

end Project.ClobPostOnly.AppendOrderFinish
