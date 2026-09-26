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


def bookAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 81,
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
  .localSet 86,
  .localGet 86,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 86
  ] [],
  .constI64 0,
  .localSet 91,
  .constI64 0,
  .localSet 87,
  .globalGet 1,
  .localSet 88
]

set_option Elab.async false in
theorem bookAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g1 capacity next : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[72]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[80]? = some (.i64 capacity))
    (hNextLocal : base.locals[81]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : orderArrayBytes n + 7 < UInt64.size)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (BookAllocSearch.bookAllocSearchFrame base
        (orderArrayBytesU n) 0 g1 capacity next 0) env) :
    wp «module» (bookAllocPrepareProg ++ rest) Q st base env := by
  have hLengthGet : base.locals[72] = .i64 (UInt64.ofNat n) := getElem_of_some hLengthLocal
  have hCapacityGet : base.locals[80] = .i64 capacity := getElem_of_some hCapacityLocal
  have hNextGet : base.locals[81] = .i64 next := getElem_of_some hNextLocal
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
        locals := (((base.locals.set 77 (.i64 (orderArrayBytesU n))).set
          82 (.i64 0)).set 78 (.i64 0)).set 79 (.i64 g1)
        values := [] } =
      BookAllocSearch.bookAllocSearchFrame base
        (orderArrayBytesU n) 0 g1 capacity next 0 := by
    unfold BookAllocSearch.bookAllocSearchFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h67 : 77 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h68 : 78 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h69 : 79 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h70 : 80 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hCapacityGet
    by_cases h71 : 81 = i
    · subst i
      simpa [List.getElem?_set, hLocals] using hNextGet
    by_cases h72 : 82 = i
    · subst i
      simp [List.getElem?_set, h68, h69]
    · simp [h67, h68, h69, h70, h71, h72]
  simp only [bookAllocPrepareProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hLengthGet, hCapacityGet, hNextGet]
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_with [hParams, hLocals, hValues, hLengthGet, hCapacityGet, hNextGet]
  simpa only [hg1, hFinalFrame] using hDone

end Project.ClobMatchFuel.BookAllocPrepare
