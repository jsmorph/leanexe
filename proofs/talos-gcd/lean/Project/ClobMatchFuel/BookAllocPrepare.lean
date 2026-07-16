import Project.ClobMatchFuel.BookAllocBump

/-!
# Erased-book allocator preparation

The full-fill branch computes the smaller book capacity and initializes the
allocator scratch locals before its free-list search.  This proof reduces that
instruction prefix to the book allocator frame.  The search, fit, and bump
proofs remain separate continuation boundaries.
-/

namespace Project.ClobMatchFuel.BookAllocPrepare

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

def bookAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 71,
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
  .localSet 76,
  .localGet 76,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 76
  ] [],
  .constI64 0,
  .localSet 81,
  .constI64 0,
  .localSet 77,
  .globalGet 1,
  .localSet 78
]

set_option Elab.async false in
theorem bookAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[62]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[70]? = some (.i64 capacity))
    (hNextLocal : base.locals[71]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : orderArrayBytes n + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (BookAllocSearch.bookAllocSearchFrame base
        (orderArrayBytesU n) 0 g1 capacity next 0) env) :
    wp «module» (bookAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[62] = .i64 (UInt64.ofNat n) := by
    apply Option.some.inj
    calc
      some base.locals[62] = base.locals[62]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat n)) := hLengthLocal
  have hCapacityGet : base.locals[70] = .i64 capacity := by
    apply Option.some.inj
    calc
      some base.locals[70] = base.locals[70]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 capacity) := hCapacityLocal
  have hNextGet : base.locals[71] = .i64 next := by
    apply Option.some.inj
    calc
      some base.locals[71] = base.locals[71]? :=
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
        locals := (((base.locals.set 67 (.i64 (orderArrayBytesU n))).set
          72 (.i64 0)).set 68 (.i64 0)).set 69 (.i64 g1)
        values := [] } =
      BookAllocSearch.bookAllocSearchFrame base
        (orderArrayBytesU n) 0 g1 capacity next 0 := by
    unfold BookAllocSearch.bookAllocSearchFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h67 : 67 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h68 : 68 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h69 : 69 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h70 : 70 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h71 : 71 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h72 : 72 = i
    · subst i
      simp [List.getElem?_set, h68, h69]
    · simp [h67, h68, h69, h70, h71, h72]
  simp only [bookAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobMatchFuel.BookAllocPrepare
