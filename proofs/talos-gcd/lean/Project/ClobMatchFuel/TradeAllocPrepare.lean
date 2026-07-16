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

macro "wp_run_prepare" "(" hParams:term "," hLocals:term ","
    hValues:term "," hLength:term "," hCapacity:term ","
    hNext:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hLength), ($hCapacity), ($hNext)])

def tradeAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 69,
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
  .localSet 78,
  .localGet 78,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 78
  ] [],
  .constI64 0,
  .localSet 83,
  .constI64 0,
  .localSet 79,
  .globalGet 1,
  .localSet 80
]

set_option Elab.async false in
theorem tradeAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[60]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[72]? = some (.i64 capacity))
    (hNextLocal : base.locals[73]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : tradeArrayBytes n + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (TradeAllocSearch.tradeAllocSearchFrame base
        (tradeArrayBytesU n) 0 g1 capacity next 0) env) :
    wp «module» (tradeAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[60] = .i64 (UInt64.ofNat n) := by
    apply Option.some.inj
    calc
      some base.locals[60] = base.locals[60]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat n)) := hLengthLocal
  have hCapacityGet : base.locals[72] = .i64 capacity := by
    apply Option.some.inj
    calc
      some base.locals[72] = base.locals[72]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 capacity) := hCapacityLocal
  have hNextGet : base.locals[73] = .i64 next := by
    apply Option.some.inj
    calc
      some base.locals[73] = base.locals[73]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 next) := hNextLocal
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
        locals := (((base.locals.set 69 (.i64 (tradeArrayBytesU n))).set
          74 (.i64 0)).set 70 (.i64 0)).set 71 (.i64 g1)
        values := [] } =
      TradeAllocSearch.tradeAllocSearchFrame base
        (tradeArrayBytesU n) 0 g1 capacity next 0 := by
    unfold TradeAllocSearch.tradeAllocSearchFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h69 : 69 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h70 : 70 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h71 : 71 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h72 : 72 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h73 : 73 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h74 : 74 = i
    · subst i
      simp [List.getElem?_set, h70, h71]
    · simp [h69, h70, h71, h72, h73, h74]
  simp only [tradeAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobMatchFuel.TradeAllocPrepare
