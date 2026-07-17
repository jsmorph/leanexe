import Project.ClobLimit.InternalPartialTradePrepare
import Project.ClobLimit.InternalTradeBump

/-!
# Partial-trade allocator preparation

The partial-fill trade branch computes the aligned stride-four capacity and
initializes the allocator scratch locals.  This module proves the exact frame
at the start of the free-list search.
-/

namespace Project.ClobLimit.InternalPartialTradeAllocPrepare

open Wasm Project.Common Project.Clob Project.ClobLimit

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

def partialTradeAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 59,
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
  .localSet 68,
  .localGet 68,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 68
  ] [],
  .constI64 0,
  .localSet 73,
  .constI64 0,
  .localSet 69,
  .globalGet 1,
  .localSet 70
  ]

set_option Elab.async false in
theorem partialTradeAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[48]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[60]? = some (.i64 capacity))
    (hNextLocal : base.locals[61]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : fixedArrayBytes n 4 + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (InternalTradeBump.allocFrame base (fixedArrayBytesU n 4) 0 g1
        capacity next 0) env) :
    wp «module» (partialTradeAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[48] = .i64 (UInt64.ofNat n) := by
    apply Option.some.inj
    calc
      some base.locals[48] = base.locals[48]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat n)) := hLengthLocal
  have hCapacityGet : base.locals[60] = .i64 capacity := by
    apply Option.some.inj
    calc
      some base.locals[60] = base.locals[60]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 capacity) := hCapacityLocal
  have hNextGet : base.locals[61] = .i64 next := by
    apply Option.some.inj
    calc
      some base.locals[61] = base.locals[61]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 next) := hNextLocal
  have hRound : (fixedArrayBytesU n 4 + 7) / 8 * 8 =
      fixedArrayBytesU n 4 :=
    fixedArrayBytesU_round n 4 hn (by decide) hbytes
  have hBytesNat : (fixedArrayBytesU n 4).toNat = fixedArrayBytes n 4 :=
    fixedArrayBytesU_toNat n 4 hn (by decide) (by omega)
  have hCapacity :
      (8 + UInt64.ofNat n * 4 * 8 + 7) / 8 * 8 =
        fixedArrayBytesU n 4 := by
    change (fixedArrayBytesU n 4 + 7) / 8 * 8 = fixedArrayBytesU n 4
    exact hRound
  have hNotSmall : ¬ fixedArrayBytesU n 4 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hBytesNat]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    unfold fixedArrayBytes
    omega
  have hFinalFrame :
      { base with
        locals := (((base.locals.set 57 (.i64 (fixedArrayBytesU n 4))).set
          62 (.i64 0)).set 58 (.i64 0)).set 59 (.i64 g1)
        values := [] } =
      InternalTradeBump.allocFrame base (fixedArrayBytesU n 4) 0 g1
        capacity next 0 := by
    unfold InternalTradeBump.allocFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h57 : 57 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h58 : 58 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h59 : 59 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h60 : 60 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h61 : 61 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h62 : 62 = i
    · subst i
      simp [List.getElem?_set, h58, h59]
    · simp [h57, h58, h59, h60, h61, h62]
  simp only [partialTradeAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobLimit.InternalPartialTradeAllocPrepare
