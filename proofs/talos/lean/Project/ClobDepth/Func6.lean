import Project.ClobDepth.Func6Loop

/-!
# Per-side fold function

Function 6 reads the order count, allocates two empty level arrays, and
folds the orders on the selected side through the level update.  The
`TerminatesWith` wrapper returns the fold state at the full order prefix and
the result root and owner values.
-/

namespace Project.ClobDepth.Func6

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.Func6Fold Project.ClobDepth.Func6Loop

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

macro "wp_run_entry" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Func6Alloc.allocFrame, Locals.get, Locals.set?, Locals.validIndex,
    List.take, List.drop, List.length, List.length_set,
    List.getElem?_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    List.headD])

set_option Elab.async false in
theorem func6_terminates
    (env : HostEnv Unit) (st : Store Unit)
    (p0 orders side g0 g2 : UInt64) (os : List OrderL)
    (hLen32 : os.length < 4294967296)
    (hBudget32 : g0.toNat + 112 +
      os.length * stepBytes os.length < 4294967296)
    (hBudget : g0.toNat + 112 + os.length * stepBytes os.length ≤
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
    TerminatesWith (m := «module») (id := 6) (initial := st) (env := env)
      [.i64 side, .i64 orders, .i64 p0]
      (fun st1 vs =>
        FoldState st os side orders g0.toNat g2 st1 os.length ∧
        vs = [.i64 (UInt64.ofNat (foldRoot os side g0.toNat os.length)),
          .i64 (UInt64.ofNat (foldOwner os side g0.toNat os.length))]) := by
  have hg0Size := UInt64.toNat_lt_size g0
  have h56 : (g0 + 56).toNat = g0.toNat + 56 := by
    rw [UInt64.toNat_add, show (56 : UInt64).toNat = 56 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have h48 : g0 + 48 = UInt64.ofNat (g0.toNat + 48) := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_add, show (48 : UInt64).toNat = 48 from rfl,
      toNat_ofNat_lt (by rw [size_eq]; omega),
      Nat.mod_eq_of_lt (by omega)]
  have h104 : g0 + 56 + 48 = UInt64.ofNat (g0.toNat + 104) := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_add, h56, show (48 : UInt64).toNat = 48 from rfl,
      toNat_ofNat_lt (by rw [size_eq]; omega),
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨⟨hLenRead, hLenBound⟩, hElems⟩ := hOrders
  refine TerminatesWith.of_wp_entry_for (f := func6Def) ?_ ?_
  · simp [«module»]
  · change wp «module» Project.ClobDepth.func6 _ st
      { params := [.i64 p0, .i64 orders, .i64 side],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    rw [Entry.func6_decomposition]
    simp only [List.append_assoc]
    simp only [Entry.func6EntryProg, List.cons_append, List.nil_append]
    wp_run_entry
    refine ⟨hLenBound, ?_⟩
    rw [hLenRead]
    apply Func6Alloc.allocProg_spec env st _ g0 g2 rfl rfl rfl
      (by omega) (by omega) hPages hGlobal0 hGlobal1 hGlobal2
    wp_run_entry
    apply Func6Alloc.allocProg_spec env _ _ (g0 + 56) (g2 + 1)
      rfl rfl rfl
      (by rw [h56]; omega)
      (by rw [Func6Alloc.allocStore_pages, h56]; omega)
      (by rw [Func6Alloc.allocStore_pages]; exact hPages)
      (Func6Alloc.allocStore_global0 st g0 g2 _ hGlobal0)
      (Func6Alloc.allocStore_global1 st g0 g2 0 hGlobal1)
      (Func6Alloc.allocStore_global2 st g0 g2 _ hGlobal2)
    wp_run_entry
    simp only [Entry.func6MinProg, List.cons_append, List.nil_append]
    wp_run_entry
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run_entry
    apply foldLoop_spec env st
      (Func6Loop.initialStore st g0 g2) _ _ os side orders g0.toNat g2
      os.length (le_refl _) hLen32 hBudget32 hBudget hPages hOrders32
      hOrders48 hOrdersCap
    · refine ⟨0, Nat.zero_le _, rfl, ?_, ?_⟩
      · refine ⟨rfl, by simp (config := { maxSteps := 10000000 }), rfl,
          rfl, ?_, ?_, ?_, rfl, rfl⟩
        · simp (config := { maxSteps := 10000000 })
        · simp (config := { maxSteps := 10000000 })
          rw [show foldOwner os side g0.toNat 0 = g0.toNat + 48 from rfl]
          exact h48
        · simp (config := { maxSteps := 10000000 })
          rw [show foldRoot os side g0.toNat 0 = g0.toNat + 104 from rfl]
          apply UInt64.toNat.inj
          rw [UInt64.toNat_add, h56,
            show (48 : UInt64).toNat = 48 from rfl,
            toNat_ofNat_lt (by rw [size_eq]; omega),
            Nat.mod_eq_of_lt (by omega)]
      · exact foldState_initial st os side orders
          (UInt64.ofNat (g0.toNat - orders.toNat)) g0 g2
          (by omega) (by omega) ⟨⟨hLenRead, hLenBound⟩, hElems⟩
          hOrders32 hOrders48
          (by
            obtain ⟨c, hc1, hc2⟩ := hOrdersCap
            rw [toNat_ofNat_lt (by rw [size_eq]; omega)]
            omega)
          (by rw [toNat_ofNat_lt (by rw [size_eq]; omega)]; omega)
          hGlobal0 hGlobal1 hGlobal2
    · intro st1 s1 hPar hLoc hSt
      have hL := hLoc.locals
      have hOwner' : s1.locals[1] =
          .i64 (UInt64.ofNat (foldOwner os side g0.toNat os.length)) := by
        apply Option.some.inj
        calc
          some s1.locals[1] = s1.locals[1]? :=
            (List.getElem?_eq_getElem (by omega)).symm
          _ = _ := hLoc.owner
      have hRoot' : s1.locals[2] =
          .i64 (UInt64.ofNat (foldRoot os side g0.toNat os.length)) := by
        apply Option.some.inj
        calc
          some s1.locals[2] = s1.locals[2]? :=
            (List.getElem?_eq_getElem (by omega)).symm
          _ = _ := hLoc.root
      simp only [Entry.func6ResultProg]
      simp (config := { maxSteps := 10000000 }) [wp_simp,
        Locals.get, Locals.set?,
        List.take, List.drop, List.length, List.length_set,
        func6Def, Function.numParams,
        hLoc.params, hL, hLoc.values, hOwner', hRoot']
      exact hSt

end Project.ClobDepth.Func6
