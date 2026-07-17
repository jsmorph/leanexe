import Project.ClobLimit.LimitResidualStatus
import Project.ClobMatchFuel.Allocation

/-!
# Residual `limit` order preparation

This phase copies the taker fields, reads the matched-book length, and computes
the old flat-word count and appended length.  Separate continuation boundaries
keep the field copies independent from the represented-array read.  Allocation
arithmetic begins in the next phase.
-/

namespace Project.ClobLimit.LimitResidualPrepare

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant

structure FieldsLocalsAt (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) : Prop where
  params : base.params.length = 6
  locals : base.locals.length = 53
  values : base.values = []
  bookResult : base.locals[21]? = some (.i64 data.book)
  tradesResult : base.locals[23]? = some (.i64 data.trades)
  status : base.locals[31]? = some (.i64 0)
  source : base.locals[34]? = some (.i64 data.book)
  oid : base.locals[40]? = some (.i64 order.oid)
  trader : base.locals[41]? = some (.i64 order.otrader)
  side : base.locals[42]? = some (.i64 order.oside)
  price : base.locals[43]? = some (.i64 order.oprice)
  remaining : base.locals[44]? = some (.i64 ctx.result.remaining)

structure OrderLocalsAt (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) : Prop where
  fields : FieldsLocalsAt base order ctx data
  length : base.locals[35]? =
    some (.i64 (UInt64.ofNat ctx.result.book.length))
  total : base.locals[36]? =
    some (.i64 (UInt64.ofNat ctx.result.book.length * 5))
  appendLength : base.locals[37]? =
    some (.i64 (UInt64.ofNat (ctx.result.book.length + 1)))

def lengthFrame (base : Locals) (n : Nat) : Locals :=
  { base with
    locals := ((base.locals.set 35 (.i64 (UInt64.ofNat n))).set 36
      (.i64 (UInt64.ofNat n * 5))).set 37
      (.i64 (UInt64.ofNat (n + 1)))
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem residualOrderFieldsProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, FieldsLocalsAt final order ctx data →
      wp «module» rest Q st final env) :
    wp «module» (LimitEntry.residualOrderFieldsProg ++ rest) Q st
      (LimitResidualStatus.statusFrame book order ctx data) env := by
  simp only [LimitEntry.residualOrderFieldsProg, List.cons_append,
    List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, LimitResidualStatus.statusFrame]
  apply hNext
  constructor <;>
    simp

theorem lengthFrame_orderLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hFields : FieldsLocalsAt base order ctx data) :
    OrderLocalsAt (lengthFrame base ctx.result.book.length) order ctx data := by
  rcases hFields with
    ⟨hParams, hLocals, hValues, hBookResult, hTradesResult, hStatus,
      hSource, hOid, hTrader, hSide, hPrice, hRemaining⟩
  constructor
  · refine {
      params := by simpa [lengthFrame] using hParams
      locals := by simpa [lengthFrame] using hLocals
      values := by simp [lengthFrame]
      bookResult := by
        simpa [lengthFrame] using hBookResult
      tradesResult := by
        simpa [lengthFrame] using hTradesResult
      status := by
        simpa [lengthFrame] using hStatus
      source := by
        simpa [lengthFrame] using hSource
      oid := by
        simpa [lengthFrame] using hOid
      trader := by
        simpa [lengthFrame] using hTrader
      side := by
        simpa [lengthFrame] using hSide
      price := by
        simpa [lengthFrame] using hPrice
      remaining := by
        simpa [lengthFrame] using hRemaining }
  · simp [lengthFrame, hLocals]
  · simp [lengthFrame, hLocals]
  · simp [lengthFrame, hLocals]

set_option Elab.async false in
theorem residualLengthProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hFields : FieldsLocalsAt base order ctx data)
    (hOutput : InternalLoopResult.OutputAt ctx st data)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, OrderLocalsAt final order ctx data →
      wp «module» rest Q st final env) :
    wp «module» (LimitEntry.residualLengthProg ++ rest) Q st base env := by
  let n := ctx.result.book.length
  have hN : n < UInt64.size := by omega
  have hNU : (UInt64.ofNat n).toNat = n := toNat_ofNat_lt hN
  have hOutU : (UInt64.ofNat (n + 1)).toNat = n + 1 :=
    toNat_ofNat_lt hLength
  have hAdd : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hNU, size_eq]; omega), hNU, hOutU]
  have hParams := hFields.params
  have hLocals := hFields.locals
  have hValues := hFields.values
  have hSource : base.locals[34] = .i64 data.book := by
    apply Option.some.inj
    calc
      some base.locals[34] = base.locals[34]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 data.book) := hFields.source
  have hLengthRead := hOutput.bookOwned.2.1.1
  have hLengthBound := hOutput.bookOwned.2.1.2
  simp only [LimitEntry.residualLengthProg, List.cons_append,
    List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, hParams, hLocals, hValues, hSource]
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead]
  rw [hAdd]
  apply hNext
  exact lengthFrame_orderLocals base order ctx data hFields

set_option Elab.async false in
theorem residualOrderPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hOutput : InternalLoopResult.OutputAt ctx st data)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, OrderLocalsAt final order ctx data →
      wp «module» rest Q st final env) :
    wp «module» (LimitEntry.residualOrderPrepareProg ++ rest) Q st
      (LimitResidualStatus.statusFrame book order ctx data) env := by
  simp only [LimitEntry.residualOrderPrepareProg, List.append_assoc]
  apply residualOrderFieldsProg_spec env st book order ctx data
  intro base hFields
  exact residualLengthProg_spec env st base order ctx data hFields hOutput
    hLength Q rest hNext

end Project.ClobLimit.LimitResidualPrepare
