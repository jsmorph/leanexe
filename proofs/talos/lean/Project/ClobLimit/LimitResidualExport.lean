import Project.ClobLimit.LimitResidualResult
import Project.ClobLimit.RunMatchAllocations

namespace Project.ClobLimit.LimitResidualExport

open Wasm Project.Clob Project.ClobLimit Project.ClobLimit.MatchInvariant
  Project.ClobMatchFuel.AllocatorFrame LimitResidualAllocation

structure ExportedResultAt (initial final : Store Unit) (ctx : Context)
    (data : MatchOutput.OutputData) (order : OrderL) (initialG0 : UInt64) : Prop where
  bookOwned : OwnedOrderArrayAt final (root ctx data) (capacity ctx data)
    (ctx.result.book ++ [{ order with oqty := ctx.result.remaining }])
  tradesOwned : OwnedTradeArrayAt final data.trades data.tradesCapacity ctx.result.trades
  pages : final.mem.pages = initial.mem.pages
  allocator : ∃ matched, MatchOutput.OutputAt ctx matched data ∧
    final.globals.globals = (allocated matched ctx data).globals.globals
  memoryBelow : Project.ClobMatchFuel.MemoryBelow.BytesEqBelow initial.mem final.mem initialG0.toNat

theorem of_result
    (initial matched final : Store Unit) (book bookCapacity g0 g2 g4 g5 : UInt64)
    (os : List OrderL) (order : OrderL) (limit : Nat) (data : MatchOutput.OutputData)
    (hHeapNat : (g0 + 112).toNat = g0.toNat + 112)
    (hInitial : RunMatchAllocations.AllocationFacts initial
      (RunMatchAllocations.allocationsStore initial g0 g2) book bookCapacity g0 g2 os)
    (hOutput : MatchOutput.OutputAt
      (RunMatchCorrect.runMatchContext initial os order g0 g2 g4 g5 limit) matched data)
    (hResult : LimitResidualResult.ResultAt matched final
      (RunMatchCorrect.runMatchContext initial os order g0 g2 g4 g5 limit) data order) :
    ExportedResultAt initial final
      (RunMatchCorrect.runMatchContext initial os order g0 g2 g4 g5 limit) data order g0 := by
  let ctx := RunMatchCorrect.runMatchContext initial os order g0 g2 g4 g5 limit
  exact {
    bookOwned := hResult.bookOwned
    tradesOwned := hResult.tradesOwned
    pages := hResult.pages.trans hOutput.pages
    allocator := ⟨matched, hOutput, hResult.globals⟩
    memoryBelow := by
      intro a ha
      have hInitialHeap : a < ctx.initialG0.toNat := by
        change a < (g0 + 112).toNat
        rw [hHeapNat]
        omega
      calc
        final.mem.bytes a = matched.mem.bytes a := hResult.memoryBelow a hInitialHeap
        _ = ctx.initialMem.bytes a := hOutput.memoryBelow a hInitialHeap
        _ = initial.mem.bytes a := hInitial.bytesBefore a ha }

end Project.ClobLimit.LimitResidualExport
