import Project.ClobLimit.InternalFullBookBump

/-!
# Full-book allocator preparation

The full-fill branch computes the aligned capacity of the smaller replacement
book.  It enforces the allocator's minimum size and initializes the search
scratch locals.  The resulting frame is the exact input to the full-book
free-list scan.
-/

namespace Project.ClobLimit.InternalFullBookAllocPrepare

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

def fullBookAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 61,
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
  .localSet 66,
  .localGet 66,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 66
  ] [],
  .constI64 0,
  .localSet 71,
  .constI64 0,
  .localSet 67,
  .globalGet 1,
  .localSet 68
  ]

set_option Elab.async false in
theorem fullBookAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[50]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[58]? = some (.i64 capacity))
    (hNextLocal : base.locals[59]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : fixedArrayBytes n 5 + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (InternalFullBookBump.allocFrame base (fixedArrayBytesU n 5) 0 g1
        capacity next 0) env) :
    wp «module» (fullBookAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[50] = .i64 (UInt64.ofNat n) := by
    apply Option.some.inj
    calc
      some base.locals[50] = base.locals[50]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat n)) := hLengthLocal
  have hCapacityGet : base.locals[58] = .i64 capacity := by
    apply Option.some.inj
    calc
      some base.locals[58] = base.locals[58]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 capacity) := hCapacityLocal
  have hNextGet : base.locals[59] = .i64 next := by
    apply Option.some.inj
    calc
      some base.locals[59] = base.locals[59]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 next) := hNextLocal
  have hRound : (fixedArrayBytesU n 5 + 7) / 8 * 8 =
      fixedArrayBytesU n 5 :=
    fixedArrayBytesU_round n 5 hn (by decide) hbytes
  have hBytesNat : (fixedArrayBytesU n 5).toNat = fixedArrayBytes n 5 :=
    fixedArrayBytesU_toNat n 5 hn (by decide) (by omega)
  have hCapacity :
      (8 + UInt64.ofNat n * 5 * 8 + 7) / 8 * 8 =
        fixedArrayBytesU n 5 := by
    change (fixedArrayBytesU n 5 + 7) / 8 * 8 = fixedArrayBytesU n 5
    exact hRound
  have hNotSmall : ¬ fixedArrayBytesU n 5 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hBytesNat]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    unfold fixedArrayBytes
    omega
  have hFinalFrame :
      { base with
        locals := (((base.locals.set 55 (.i64 (fixedArrayBytesU n 5))).set
          60 (.i64 0)).set 56 (.i64 0)).set 57 (.i64 g1)
        values := [] } =
      InternalFullBookBump.allocFrame base (fixedArrayBytesU n 5) 0 g1
        capacity next 0 := by
    unfold InternalFullBookBump.allocFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h55 : 55 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h56 : 56 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h57 : 57 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h58 : 58 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h59 : 59 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h60 : 60 = i
    · subst i
      simp [List.getElem?_set, h56, h57]
    · simp [h55, h56, h57, h58, h59, h60]
  simp only [fullBookAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hLengthGet, hCapacityGet,
    hNextGet)
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobLimit.InternalFullBookAllocPrepare
