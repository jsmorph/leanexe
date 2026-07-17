import Project.ClobLimit.LimitResidualResult
import Project.ClobLimit.RunMatchAllocations

/-!
# Exported residual result

This module translates the residual result from the matcher-output store to
the exported function's initial store.  It composes both below-heap memory
frames and states the public allocator globals and owned result arrays.
-/

namespace Project.ClobLimit.LimitResidualExport

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

structure ExportedResultAt (initial final : Store Unit) (ctx : Context)
    (data : InternalLoopResult.OutputData) (order : OrderL)
    (initialG0 : UInt64) : Prop where
  bookOwned : OwnedOrderArrayAt final (data.g0 + 48)
    (orderArrayBytesU (ctx.result.book.length + 1))
    (ctx.result.book ++ [{ order with oqty := ctx.result.remaining }])
  tradesOwned : OwnedTradeArrayAt final data.trades data.tradesCapacity
    ctx.result.trades
  pages : final.mem.pages = initial.mem.pages
  global0 : final.globals.globals[0]? = some
    (.i64 (data.g0 + 48 + orderArrayBytesU (ctx.result.book.length + 1)))
  global1 : final.globals.globals[1]? = some (.i64 0)
  global2 : final.globals.globals[2]? = some (.i64 (ctx.expectedG2 + 1))
  memoryBelow : BytesEqBelow initial.mem final.mem initialG0.toNat

theorem of_result
    (initial matched final : Store Unit) (book bookCapacity g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL) (limit : Nat)
    (data : InternalLoopResult.OutputData)
    (hHeapNat : (g0 + 112).toNat = g0.toNat + 112)
    (hInitial : RunMatchAllocations.AllocationFacts initial
      (RunMatchAllocations.allocationsStore initial g0 g2)
      book bookCapacity g0 g2 os)
    (hOutput : InternalLoopResult.OutputAt
      (RunMatchCorrect.runMatchContext initial os order g0 g2 limit)
      matched data)
    (hResult : LimitResidualResult.ResultAt matched final
      (RunMatchCorrect.runMatchContext initial os order g0 g2 limit)
      data order) :
    ExportedResultAt initial final
      (RunMatchCorrect.runMatchContext initial os order g0 g2 limit)
      data order g0 := by
  let ctx := RunMatchCorrect.runMatchContext initial os order g0 g2 limit
  have hGlobal0Length : 0 < matched.globals.globals.length :=
    (List.getElem?_eq_some_iff.mp hOutput.global0).choose
  have hGlobal1Length : 1 < matched.globals.globals.length :=
    (List.getElem?_eq_some_iff.mp hOutput.global1).choose
  have hGlobal2Length : 2 < matched.globals.globals.length :=
    (List.getElem?_eq_some_iff.mp hOutput.global2).choose
  exact {
    bookOwned := hResult.bookOwned
    tradesOwned := hResult.tradesOwned
    pages := by
      calc
        final.mem.pages = matched.mem.pages := hResult.pages
        _ = ctx.initialPages := hOutput.pages
        _ = initial.mem.pages := rfl
    global0 := by
      rw [hResult.globals]
      simp [hGlobal0Length]
    global1 := by
      rw [hResult.globals]
      simpa [List.getElem?_set, hGlobal1Length] using hOutput.global1
    global2 := by
      rw [hResult.globals]
      simp [hGlobal2Length]
    memoryBelow := by
      intro a ha
      have hInitialHeap : a < ctx.initialG0.toNat := by
        change a < (g0 + 112).toNat
        rw [hHeapNat]
        omega
      have hCurrentHeap : a < data.g0.toNat :=
        hInitialHeap.trans_le hOutput.heapMono
      calc
        final.mem.bytes a = matched.mem.bytes a :=
          hResult.memoryBelow a hCurrentHeap
        _ = ctx.initialMem.bytes a := hOutput.memoryBelow a hInitialHeap
        _ = initial.mem.bytes a := by
          change (RunMatchAllocations.allocationsStore initial g0 g2).mem.bytes
              a = initial.mem.bytes a
          exact hInitial.bytesBefore a ha }

end Project.ClobLimit.LimitResidualExport
