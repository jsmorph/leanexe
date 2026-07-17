import Project.ClobMatchFuel.PartialBookAllocBump

/-!
# Partial-fill book allocator preparation

The partial-fill branch computes the fresh-book capacity and initializes the
allocator scratch locals before its free-list search.  This proof reduces that
instruction prefix to the partial-book allocator frame.  The search, fit, and
bump proofs remain separate continuation boundaries.
-/

namespace Project.ClobMatchFuel.PartialBookAllocPrepare

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

def partialBookAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 68,
  .constI64 5,
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
  .localSet 79,
  .localGet 79,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 79
  ] [],
  .constI64 0,
  .localSet 84,
  .constI64 0,
  .localSet 80,
  .globalGet 1,
  .localSet 81
]

set_option Elab.async false in
theorem partialBookAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[59]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[73]? = some (.i64 capacity))
    (hNextLocal : base.locals[74]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : orderArrayBytes n + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (PartialBookAllocSearch.bookAllocSearchFrame base
        (orderArrayBytesU n) 0 g1 capacity next 0) env) :
    wp «module» (partialBookAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[59] = .i64 (UInt64.ofNat n) := by
    apply Option.some.inj
    calc
      some base.locals[59] = base.locals[59]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat n)) := hLengthLocal
  have hCapacityGet : base.locals[73] = .i64 capacity := by
    apply Option.some.inj
    calc
      some base.locals[73] = base.locals[73]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 capacity) := hCapacityLocal
  have hNextGet : base.locals[74] = .i64 next := by
    apply Option.some.inj
    calc
      some base.locals[74] = base.locals[74]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 next) := hNextLocal
  have hRound : (orderArrayBytesU n + 7) / 8 * 8 =
      orderArrayBytesU n :=
    fixedArrayBytesU_round n 5 hn (by decide) hbytes
  have hBytesNat : (orderArrayBytesU n).toNat = orderArrayBytes n :=
    fixedArrayBytesU_toNat n 5 hn (by decide) (by
      change fixedArrayBytes n 5 + 7 < UInt64.size at hbytes
      omega)
  have hCapacity :
      (8 + UInt64.ofNat n * 5 * 8 + 7) / 8 * 8 =
        orderArrayBytesU n := by
    change (orderArrayBytesU n + 7) / 8 * 8 = orderArrayBytesU n
    exact hRound
  have hNotSmall : ¬ orderArrayBytesU n < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hBytesNat]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hFinalFrame :
      { base with
        locals := (((base.locals.set 70 (.i64 (orderArrayBytesU n))).set
          75 (.i64 0)).set 71 (.i64 0)).set 72 (.i64 g1)
        values := [] } =
      PartialBookAllocSearch.bookAllocSearchFrame base
        (orderArrayBytesU n) 0 g1 capacity next 0 := by
    unfold PartialBookAllocSearch.bookAllocSearchFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h70 : 70 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h71 : 71 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h72 : 72 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h73 : 73 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h74 : 74 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h75 : 75 = i
    · subst i
      simp [List.getElem?_set, h71, h72]
    · simp [h70, h71, h72, h73, h74, h75]
  simp only [partialBookAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobMatchFuel.PartialBookAllocPrepare
