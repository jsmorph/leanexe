import Project.ClobLimit.LimitResidualPrepare

/-!
# Residual `limit` allocator preparation

This phase computes the aligned capacity for the appended order array.  It
initializes the free-list predecessor, current-node, and result locals.  The
following proof can treat the generated search and bump allocation separately.
-/

namespace Project.ClobLimit.LimitResidualAllocPrepare

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant Project.ClobMatchFuel.Allocation

structure AllocLocalsAt (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) : Prop where
  orderLocals : LimitResidualPrepare.OrderLocalsAt base order ctx data
  need : base.locals[47]? =
    some (.i64 (orderArrayBytesU (ctx.result.book.length + 1)))
  previous : base.locals[48]? = some (.i64 0)
  current : base.locals[49]? = some (.i64 0)
  result : base.locals[52]? = some (.i64 0)

def allocPrepareFrame (base : Locals) (n : Nat) : Locals :=
  { base with
    locals := (((base.locals.set 47
      (.i64 (orderArrayBytesU (n + 1)))).set 52 (.i64 0)).set 48
      (.i64 0)).set 49 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

theorem allocPrepareFrame_allocLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data) :
    AllocLocalsAt (allocPrepareFrame base ctx.result.book.length)
      order ctx data := by
  rcases hOrder with ⟨hFields, hLength, hTotal, hAppendLength⟩
  rcases hFields with
    ⟨hParams, hLocals, hValues, hBookResult, hTradesResult, hStatus,
      hSource, hOid, hTrader, hSide, hPrice, hRemaining⟩
  constructor
  · constructor
    · refine {
        params := by simpa [allocPrepareFrame] using hParams
        locals := by simpa [allocPrepareFrame] using hLocals
        values := by simp [allocPrepareFrame]
        bookResult := by simpa [allocPrepareFrame] using hBookResult
        tradesResult := by simpa [allocPrepareFrame] using hTradesResult
        status := by simpa [allocPrepareFrame] using hStatus
        source := by simpa [allocPrepareFrame] using hSource
        oid := by simpa [allocPrepareFrame] using hOid
        trader := by simpa [allocPrepareFrame] using hTrader
        side := by simpa [allocPrepareFrame] using hSide
        price := by simpa [allocPrepareFrame] using hPrice
        remaining := by simpa [allocPrepareFrame] using hRemaining }
    · simpa [allocPrepareFrame] using hLength
    · simpa [allocPrepareFrame] using hTotal
    · simpa [allocPrepareFrame] using hAppendLength
  · simp [allocPrepareFrame, hLocals]
  · simp [allocPrepareFrame, hLocals]
  · simp [allocPrepareFrame, hLocals]
  · simp [allocPrepareFrame, hLocals]

set_option Elab.async false in
theorem residualAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data)
    (hOutput : InternalLoopResult.OutputAt ctx st data)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 <
      UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, AllocLocalsAt final order ctx data →
      wp «module» rest Q st final env) :
    wp «module» (LimitEntry.residualAllocPrepareProg ++ rest) Q st
      base env := by
  let n := ctx.result.book.length
  have hParams := hOrder.fields.params
  have hLocals := hOrder.fields.locals
  have hValues := hOrder.fields.values
  have hAppendLength : base.locals[37] =
      .i64 (UInt64.ofNat (n + 1)) := by
    apply Option.some.inj
    calc
      some base.locals[37] = base.locals[37]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat (n + 1))) := hOrder.appendLength
  have hLength' : n + 1 < UInt64.size := by simpa [n] using hLength
  have hBytes' : orderArrayBytes (n + 1) + 7 < UInt64.size := by
    simpa [n] using hBytes
  have hNU : (UInt64.ofNat n).toNat = n :=
    toNat_ofNat_lt (by omega)
  have hOutU : (UInt64.ofNat (n + 1)).toNat = n + 1 :=
    toNat_ofNat_lt hLength'
  have hAdd : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hNU, size_eq]; omega), hNU, hOutU]
  have hRound :
      (orderArrayBytesU (n + 1) + 7) / 8 * 8 =
        orderArrayBytesU (n + 1) :=
    fixedArrayBytesU_round (n + 1) 5 hLength' (by decide) hBytes'
  have hBytesNat :
      (orderArrayBytesU (n + 1)).toNat = orderArrayBytes (n + 1) :=
    fixedArrayBytesU_toNat (n + 1) 5 hLength' (by decide) (by
      change fixedArrayBytes (n + 1) 5 + 7 < UInt64.size at hBytes'
      omega)
  have hCapacity :
      (8 + (UInt64.ofNat n + 1) * 5 * 8 + 7) / 8 * 8 =
        orderArrayBytesU (n + 1) := by
    rw [hAdd]
    change (orderArrayBytesU (n + 1) + 7) / 8 * 8 =
      orderArrayBytesU (n + 1)
    exact hRound
  have hNotSmall : ¬orderArrayBytesU (n + 1) < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hBytesNat]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    unfold orderArrayBytes fixedArrayBytes
    omega
  simp only [LimitEntry.residualAllocPrepareProg, List.cons_append,
    List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, hParams, hLocals, hValues, hAppendLength]
  rw [hCapacity, if_neg hNotSmall]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, hParams, hLocals]
  simp only [hOutput.global1]
  apply hNext
  exact allocPrepareFrame_allocLocals base order ctx data hOrder

end Project.ClobLimit.LimitResidualAllocPrepare
