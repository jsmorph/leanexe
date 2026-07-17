import Project.ClobLimit.LimitResidualBump

/-!
# Complete residual `limit` allocation

The allocation finish increments global 2, stores the appended length, and
initializes the copy counter.  This module composes that suffix with capacity
preparation, the empty free-list search, and the bump fallback.  Its output
frame exposes the source, target, and counter facts consumed by the copy loop.
-/

namespace Project.ClobLimit.LimitResidualAlloc

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation

structure BumpLocalsAt (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 : UInt64) : Prop where
  orderLocals : LimitResidualPrepare.OrderLocalsAt base order ctx data
  result : base.locals[52]? = some (.i64 (g0 + 48))

structure CopyLocalsAt (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 : UInt64) : Prop where
  orderLocals : LimitResidualPrepare.OrderLocalsAt base order ctx data
  target : base.locals[38]? = some (.i64 (g0 + 48))
  counter : base.locals[39]? = some (.i64 0)

def copyFrame (base : Locals) (g0 : UInt64) : Locals :=
  { base with
    locals := (base.locals.set 38 (.i64 (g0 + 48))).set 39 (.i64 0)
    values := [] }

def allocGlobals (st : Store Unit) (g0 g2 need : UInt64) : List Value :=
  (fixedArrayAllocBumpStore st g0 need 5).globals.globals.set 2
    (.i64 (g2 + 1))

def allocMem (st : Store Unit) (g0 need length : UInt64) : Mem :=
  (fixedArrayAllocBumpStore st g0 need 5).mem.write64
    (g0 + 48).toUInt32 length

def allocStore (st : Store Unit) (g0 g2 need length : UInt64) : Store Unit :=
  { fixedArrayAllocBumpStore st g0 need 5 with
    globals := { globals := allocGlobals st g0 g2 need }
    mem := allocMem st g0 need length }

set_option maxRecDepth 1048576

theorem bumpFrame_bumpLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 : UInt64)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data) :
    BumpLocalsAt
      (LimitResidualBump.bumpFrame base g0
        (orderArrayBytesU (ctx.result.book.length + 1)))
      order ctx data g0 := by
  rcases hAlloc.orderLocals with ⟨hFields, hLength, hTotal, hAppendLength⟩
  rcases hFields with
    ⟨hParams, hLocals, hValues, hBookResult, hTradesResult, hStatus,
      hSource, hOid, hTrader, hSide, hPrice, hRemaining⟩
  constructor
  · constructor
    · refine {
        params := by simpa [LimitResidualBump.bumpFrame] using hParams
        locals := by simpa [LimitResidualBump.bumpFrame] using hLocals
        values := by simp [LimitResidualBump.bumpFrame]
        bookResult := by
          simpa [LimitResidualBump.bumpFrame] using hBookResult
        tradesResult := by
          simpa [LimitResidualBump.bumpFrame] using hTradesResult
        status := by simpa [LimitResidualBump.bumpFrame] using hStatus
        source := by simpa [LimitResidualBump.bumpFrame] using hSource
        oid := by simpa [LimitResidualBump.bumpFrame] using hOid
        trader := by simpa [LimitResidualBump.bumpFrame] using hTrader
        side := by simpa [LimitResidualBump.bumpFrame] using hSide
        price := by simpa [LimitResidualBump.bumpFrame] using hPrice
        remaining := by
          simpa [LimitResidualBump.bumpFrame] using hRemaining }
    · simpa [LimitResidualBump.bumpFrame] using hLength
    · simpa [LimitResidualBump.bumpFrame] using hTotal
    · simpa [LimitResidualBump.bumpFrame] using hAppendLength
  · simp [LimitResidualBump.bumpFrame, hLocals]

theorem copyFrame_copyLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 : UInt64)
    (hBump : BumpLocalsAt base order ctx data g0) :
    CopyLocalsAt (copyFrame base g0) order ctx data g0 := by
  rcases hBump.orderLocals with ⟨hFields, hLength, hTotal, hAppendLength⟩
  rcases hFields with
    ⟨hParams, hLocals, hValues, hBookResult, hTradesResult, hStatus,
      hSource, hOid, hTrader, hSide, hPrice, hRemaining⟩
  constructor
  · constructor
    · refine {
        params := by simpa [copyFrame] using hParams
        locals := by simpa [copyFrame] using hLocals
        values := by simp [copyFrame]
        bookResult := by simpa [copyFrame] using hBookResult
        tradesResult := by simpa [copyFrame] using hTradesResult
        status := by simpa [copyFrame] using hStatus
        source := by simpa [copyFrame] using hSource
        oid := by simpa [copyFrame] using hOid
        trader := by simpa [copyFrame] using hTrader
        side := by simpa [copyFrame] using hSide
        price := by simpa [copyFrame] using hPrice
        remaining := by simpa [copyFrame] using hRemaining }
    · simpa [copyFrame] using hLength
    · simpa [copyFrame] using hTotal
    · simpa [copyFrame] using hAppendLength
  · simp [copyFrame, hLocals]
  · simp [copyFrame, hLocals]

set_option Elab.async false in
theorem residualAllocFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 g2 : UInt64)
    (hBump : BumpLocalsAt base order ctx data g0)
    (hRoot : (g0 + 48).toNat = g0.toNat + 48)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536)
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, CopyLocalsAt final order ctx data g0 →
      wp «module» rest Q
        (allocStore st g0 g2
          (orderArrayBytesU (ctx.result.book.length + 1))
          (UInt64.ofNat (ctx.result.book.length + 1))) final env) :
    wp «module» (LimitEntry.residualAllocFinishProg ++ rest) Q
      (fixedArrayAllocBumpStore st g0
        (orderArrayBytesU (ctx.result.book.length + 1)) 5) base env := by
  let need := orderArrayBytesU (ctx.result.book.length + 1)
  let st1 := fixedArrayAllocBumpStore st g0 need 5
  have hParams := hBump.orderLocals.fields.params
  have hLocals := hBump.orderLocals.fields.locals
  have hValues := hBump.orderLocals.fields.values
  have hLength : base.locals[37] =
      .i64 (UInt64.ofNat (ctx.result.book.length + 1)) := by
    apply Option.some.inj
    calc
      some base.locals[37] = base.locals[37]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat (ctx.result.book.length + 1))) :=
        hBump.orderLocals.appendLength
  have hResult : base.locals[52] = .i64 (g0 + 48) := by
    apply Option.some.inj
    calc
      some base.locals[52] = base.locals[52]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (g0 + 48)) := hBump.result
  have hg2' : st1.globals.globals[2]? = some (.i64 g2) := by
    exact fixedArrayAllocBumpStore_global_of_ne_zero st g0 need 5 2
      (.i64 g2) (by decide) hg2
  dsimp only [st1, need] at hg2'
  have hRootBound : (g0.toNat + 48) % 4294967296 + 8 ≤
      (fixedArrayAllocBumpStore st g0
        (orderArrayBytesU (ctx.result.book.length + 1)) 5).mem.pages *
        65536 := by
    rw [Nat.mod_eq_of_lt (by omega),
      fixedArrayAllocBumpStore_pages]
    omega
  simp only [LimitEntry.residualAllocFinishProg, List.cons_append,
    List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, hParams, hLocals, hValues, hLength, hResult]
  simp only [hg2']
  rw [if_neg (Nat.not_lt.mpr hRootBound)]
  have hContinue := hNext (copyFrame base g0)
    (copyFrame_copyLocals base order ctx data g0 hBump)
  simpa [allocStore, allocGlobals, allocMem, copyFrame,
    toUInt32_eq_ofNat, hRoot, UInt64.ofNat_add] using hContinue

set_option Elab.async false in
theorem residualAllocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 <
      UInt64.size)
    (hTop : (data.g0 + 48 + orderArrayBytesU
      (ctx.result.book.length + 1)).toNat =
        data.g0.toNat + 48 +
          (orderArrayBytesU (ctx.result.book.length + 1)).toNat)
    (hFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat ≤
        st.mem.pages * 65536)
    (hOutput : InternalLoopResult.OutputAt ctx st data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, CopyLocalsAt final order ctx data data.g0 →
      wp «module» rest Q
        (allocStore st data.g0 ctx.expectedG2
          (orderArrayBytesU (ctx.result.book.length + 1))
          (UInt64.ofNat (ctx.result.book.length + 1))) final env) :
    wp «module» (LimitEntry.residualAllocProg ++ rest) Q st base env := by
  have hNeedNat :
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat =
        orderArrayBytes (ctx.result.book.length + 1) :=
    fixedArrayBytesU_toNat (ctx.result.book.length + 1) 5 hLength
      (by decide) (by
        change fixedArrayBytes (ctx.result.book.length + 1) 5 + 7 <
          UInt64.size at hBytes
        omega)
  have hNeed8 : 8 ≤
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat := by
    rw [hNeedNat]
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hRoot : (data.g0 + 48).toNat = data.g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat data.g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hFinish := residualAllocFinishProg_spec env st
    (LimitResidualBump.bumpFrame base data.g0
      (orderArrayBytesU (ctx.result.book.length + 1)))
    order ctx data data.g0 ctx.expectedG2
    (bumpFrame_bumpLocals base order ctx data data.g0 hAlloc) hRoot
    (by omega) (by omega) hOutput.global2 Q rest hNext
  have hBump := LimitResidualBump.residualAllocBumpProg_spec env st base
    order ctx data data.g0 hAlloc hNeed8 hTop hFit32 hFit hOutput.pageLimit
    hOutput.global0 Q (LimitEntry.residualAllocFinishProg ++ rest) hFinish
  have hSearch := LimitResidualBump.residualAllocSearchProg_empty env st base
    order ctx data hAlloc Q
    (LimitEntry.residualAllocBumpProg ++
      LimitEntry.residualAllocFinishProg ++ rest) hBump
  unfold LimitEntry.residualAllocProg
  simpa only [List.append_assoc] using hSearch

end Project.ClobLimit.LimitResidualAlloc
