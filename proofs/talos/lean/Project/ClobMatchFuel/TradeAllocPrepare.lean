import Project.ClobMatchFuel.TradeAllocBump

/-!
# Trade allocator preparation

The common trade branch computes the fresh-array capacity and initializes the
allocator scratch locals before its free-list search.  This proof reduces that
instruction prefix to the shared trade allocator frame.  The search, fit, and
bump proofs remain separate continuation boundaries.
-/

namespace Project.ClobMatchFuel.TradeAllocPrepare

open Wasm Project.Common Project.Clob Project.Runtime Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576


def tradeAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 79,
  .constI64 4,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet 88,
  .localGet 88,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 88
  ] [],
  .constI64 0,
  .localSet 93,
  .constI64 0,
  .localSet 89,
  .globalGet 1,
  .localSet 90
]

set_option Elab.async false in
theorem tradeAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[70]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[82]? = some (.i64 capacity))
    (hNextLocal : base.locals[83]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : tradeArrayBytes n + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (TradeAllocSearch.tradeAllocSearchFrame base
        (tradeArrayBytesU n) 0 g1 capacity next 0) env) :
    wp «module» (tradeAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[70] = .i64 (UInt64.ofNat n) := getElem_of_some hLengthLocal
  have hCapacityGet : base.locals[82] = .i64 capacity := getElem_of_some hCapacityLocal
  have hNextGet : base.locals[83] = .i64 next := getElem_of_some hNextLocal
  have hRound : (tradeArrayBytesU n + 7) / 8 * 8 =
      tradeArrayBytesU n :=
    fixedArrayBytesU_round n 4 hn (by decide) hbytes
  have hBytesNat : (tradeArrayBytesU n).toNat = tradeArrayBytes n :=
    fixedArrayBytesU_toNat n 4 hn (by decide) (by
      change fixedArrayBytes n 4 + 7 < UInt64.size at hbytes
      omega)
  have hCapacity :
      (8 + UInt64.ofNat n * 4 * 8 + 7) / 8 * 8 =
        tradeArrayBytesU n := by
    change (tradeArrayBytesU n + 7) / 8 * 8 = tradeArrayBytesU n
    exact hRound
  have hNotSmall : ¬ tradeArrayBytesU n < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hBytesNat]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    unfold tradeArrayBytes fixedArrayBytes
    omega
  have hFinalFrame :
      { base with
        locals := (((base.locals.set 79 (.i64 (tradeArrayBytesU n))).set
          84 (.i64 0)).set 80 (.i64 0)).set 81 (.i64 g1)
        values := [] } =
      TradeAllocSearch.tradeAllocSearchFrame base
        (tradeArrayBytesU n) 0 g1 capacity next 0 := by
    unfold TradeAllocSearch.tradeAllocSearchFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h69 : 79 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h70 : 80 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h71 : 81 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h72 : 82 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h73 : 83 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h74 : 84 = i
    · subst i
      simp [List.getElem?_set, h70, h71]
    · simp [h69, h70, h71, h72, h73, h74]
  simp only [tradeAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hLengthGet, hCapacityGet, hNextGet]
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_with [hParams, hLocals, hValues, hLengthGet, hCapacityGet, hNextGet]
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobMatchFuel.TradeAllocPrepare
