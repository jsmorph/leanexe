import Project.ClobDepth.Func6

/-!
# Exported depth function

Function 7 folds both sides through function 6 and returns the two owned
level arrays.  The result predicate states ownership of both arrays with the
exact source side folds, the preserved orders representation, the exact
allocator globals, page equality, and the byte frame below the initial heap
top.
-/

namespace Project.ClobDepth.Func7

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.Func6Fold Project.ClobDepth.Func6Loop

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

structure Result (st0 st : Store Unit) (os : List OrderL)
    (orders : UInt64) (g0n : Nat) (g2 : UInt64) : Prop where
  pages : st.mem.pages = st0.mem.pages
  bidsOwned : OwnedLevelArrayAt st
    (UInt64.ofNat (foldRoot os 0 g0n os.length))
    (UInt64.ofNat (foldCap os 0 os.length)) (depthSideL os 0)
  asksOwned : OwnedLevelArrayAt st
    (UInt64.ofNat
      (foldRoot os 1 (foldTop os 0 g0n os.length) os.length))
    (UInt64.ofNat (foldCap os 1 os.length)) (depthSideL os 1)
  ordersRep : OrdersAt st orders os
  global0 : st.globals.globals[0]? = some (.i64 (UInt64.ofNat
    (foldTop os 1 (foldTop os 0 g0n os.length) os.length)))
  global1 : st.globals.globals[1]? = some (.i64 0)
  global2 : st.globals.globals[2]? = some (.i64
    (g2 + 2 + UInt64.ofNat (matchCount os 0 os.length) + 2 +
      UInt64.ofNat (matchCount os 1 os.length)))
  bytesBefore : ∀ a : Nat, a < g0n →
    st.mem.bytes a = st0.mem.bytes a

set_option Elab.async false in
theorem func7_terminates
    (env : HostEnv Unit) (st : Store Unit)
    (orders g0 g2 : UInt64) (os : List OrderL)
    (hLen32 : os.length < 4294967296)
    (hBudget32 : g0.toNat + 224 +
      2 * (os.length * stepBytes os.length) < 4294967296)
    (hBudget : g0.toNat + 224 + 2 * (os.length * stepBytes os.length) ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hOrders : OrdersAt st orders os)
    (hOrders32 :
      orders.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOrders48 : 48 ≤ orders.toNat)
    (hOrdersCap : ∃ c : Nat,
      fixedArrayBytes os.length 5 ≤ c ∧ orders.toNat + c ≤ g0.toNat)
    (hGlobal0 : st.globals.globals[0]? = some (.i64 g0))
    (hGlobal1 : st.globals.globals[1]? = some (.i64 0))
    (hGlobal2 : st.globals.globals[2]? = some (.i64 g2)) :
    TerminatesWith (m := «module») (id := 7) (initial := st) (env := env)
      [.i64 orders]
      (fun st2 vs =>
        Result st st2 os orders g0.toNat g2 ∧
        vs = [.i64 (UInt64.ofNat
            (foldRoot os 1 (foldTop os 0 g0.toNat os.length) os.length)),
          .i64 (UInt64.ofNat (foldRoot os 0 g0.toNat os.length))]) := by
  have hTop1Le := foldTop_le os 0 g0.toNat os.length os.length
    (le_refl _) (le_refl _)
  have hTop1Ge := foldTop_ge os 0 g0.toNat os.length
  have hTop1_32 : foldTop os 0 g0.toNat os.length < 4294967296 := by
    omega
  have hT1 : (UInt64.ofNat (foldTop os 0 g0.toNat os.length)).toNat =
      foldTop os 0 g0.toNat os.length := by u64_omega
  refine TerminatesWith.of_wp_entry_for (f := func7Def) ?_ ?_
  · simp [«module»]
  · change wp «module» Project.ClobDepth.func7 _ st
      { params := [.i64 orders],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    simp only [Project.ClobDepth.func7]
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Locals.get, Locals.set?, List.length]
    refine wp_call_tw (Func6.func6_terminates env st 0 orders 0 g0 g2 os
      hLen32 (by omega) (by omega) hPages hOrders hOrders32 hOrders48
      hOrdersCap hGlobal0 hGlobal1 hGlobal2) ?_
    intro st1 vs ⟨hSt1, hvs⟩
    subst hvs
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Locals.get, Locals.set?, List.length]
    have hOrdersCap1 : ∃ c : Nat,
        fixedArrayBytes os.length 5 ≤ c ∧
        orders.toNat + c ≤
          (UInt64.ofNat (foldTop os 0 g0.toNat os.length)).toNat := by
      obtain ⟨c, hc1, hc2⟩ := hOrdersCap
      exact ⟨c, hc1, by rw [hT1]; omega⟩
    refine wp_call_tw (Func6.func6_terminates env st1 0 orders 1
      (UInt64.ofNat (foldTop os 0 g0.toNat os.length))
      (g2 + 2 + UInt64.ofNat (matchCount os 0 os.length)) os
      hLen32 (by rw [hT1]; omega)
      (by rw [hT1, hSt1.pages]; omega)
      (by rw [hSt1.pages]; exact hPages)
      hSt1.ordersRep hOrders32 hOrders48 hOrdersCap1
      hSt1.global0 hSt1.global1 hSt1.global2) ?_
    intro st2 vs2 ⟨hSt2, hvs2⟩
    subst hvs2
    rw [hT1] at hSt2
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Locals.get, Locals.set?, List.take, List.drop, List.length,
      func7Def, Function.numParams]
    have hRoot0Cap := foldRoot_add_cap os 0 g0.toNat os.length
    have hRoot0Ge := foldRoot_ge os 0 g0.toNat os.length
    have hCap0Bytes := foldCap_bytes os 0 os.length
    have hRoot0Nat :
        (UInt64.ofNat (foldRoot os 0 g0.toNat os.length)).toNat =
        foldRoot os 0 g0.toNat os.length := by u64_omega
    have hCap0Nat :
        (UInt64.ofNat (foldCap os 0 os.length)).toNat =
        foldCap os 0 os.length := by u64_omega
    have hBidsBase : OwnedLevelArrayAt st1
        (UInt64.ofNat (foldRoot os 0 g0.toNat os.length))
        (UInt64.ofNat (foldCap os 0 os.length))
        (depthSideL os 0) := by
      rw [← foldLevels_full os 0]
      exact hSt1.resultOwned
    have hCapD : fixedArrayBytes (depthSideL os 0).length 2 ≤
        foldCap os 0 os.length := by
      rw [← foldLevels_full os 0]
      exact hCap0Bytes
    have hBids : OwnedLevelArrayAt st2
        (UInt64.ofNat (foldRoot os 0 g0.toNat os.length))
        (UInt64.ofNat (foldCap os 0 os.length)) (depthSideL os 0) := by
      apply hBidsBase.frame_region
        (by rw [hRoot0Nat]
            omega)
        (by rw [hRoot0Nat]
            omega)
        (by rw [hCap0Nat]
            exact hCapD)
        hSt2.pages
      intro a _ ha
      apply hSt2.bytesBefore
      rw [hRoot0Nat, hCap0Nat] at ha
      omega
    rw [Nat.mod_eq_of_lt
      (show foldTop os 0 g0.toNat os.length < 18446744073709551616 by
        omega)]
    refine ⟨?_, rfl⟩
    refine {
      pages := hSt2.pages.trans hSt1.pages
      bidsOwned := hBids
      asksOwned := ?_
      ordersRep := hSt2.ordersRep
      global0 := hSt2.global0
      global1 := hSt2.global1
      global2 := hSt2.global2
      bytesBefore := ?_ }
    · rw [← foldLevels_full os 1]
      exact hSt2.resultOwned
    · intro a ha
      rw [hSt2.bytesBefore a (by omega)]
      exact hSt1.bytesBefore a ha

end Project.ClobDepth.Func7
