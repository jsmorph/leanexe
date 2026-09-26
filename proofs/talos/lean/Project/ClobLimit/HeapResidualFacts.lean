import Project.ClobMatchFuel.LoopResult

namespace Project.ClobLimit.HeapResidualFacts
open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.LoopResult
open Project.ClobMatchFuel.AllocatorFrame

structure Geometry (ctx : Context) (st : Store Unit) (data : OutputData) : Prop where
  book48 : 48 ≤ data.book.toNat
  book32 : data.book.toNat + fixedArrayBytes ctx.result.book.length 5 < 4294967296
  bookCapacity : fixedArrayBytes ctx.result.book.length 5 ≤ data.bookCapacity.toNat
  bookBelow : data.book.toNat + data.bookCapacity.toNat ≤ data.g0.toNat
  bookFree : FreeListSeparatedFromFixedArray data.nodes data.book data.bookCapacity
  trades48 : 48 ≤ data.trades.toNat
  trades32 : data.trades.toNat + fixedArrayBytes ctx.result.trades.length 4 < 4294967296
  tradesCapacity : fixedArrayBytes ctx.result.trades.length 4 ≤ data.tradesCapacity.toNat
  tradesBelow : data.trades.toNat + data.tradesCapacity.toNat ≤ data.g0.toNat
  tradesFree : FreeListSeparatedFromFixedArray data.nodes data.trades data.tradesCapacity
  nodesBelow : ∀ node ∈ data.nodes, node.root.toNat + node.capacity.toNat ≤ data.g0.toNat
  heapLimit : data.g0.toNat ≤ ctx.limit
  pageLimit : st.mem.pages ≤ 65536
  addressLimit : ctx.limit < 4294967296
  memoryLimit : ctx.limit ≤ st.mem.pages * 65536

theorem of_output (h : OutputAt ctx st data) (hRemaining : ctx.result.remaining ≠ 0) :
    Geometry ctx st data := by
  obtain ⟨running, frame, facts, hb, hbc, ht, htc, hg, hn, hSource⟩ := h.residual hRemaining
  have hData : data = runningOutputData running := by
    cases data
    simp_all [runningOutputData]
  subst data
  refine {
    book48 := facts.book48
    book32 := ?_
    bookCapacity := ?_
    bookBelow := facts.bookBelow
    bookFree := facts.bookFree
    trades48 := facts.trades48
    trades32 := ?_
    tradesCapacity := ?_
    tradesBelow := facts.tradesBelow
    tradesFree := facts.tradesFree
    nodesBelow := facts.nodesBelow
    heapLimit := ?_
    pageLimit := facts.pageLimit
    addressLimit := facts.addressLimit
    memoryLimit := facts.memoryLimit }
  · simpa [runningOutputData, hSource, RunningData.sourceState] using facts.book32
  · simpa [runningOutputData, hSource, RunningData.sourceState] using facts.bookCapacity
  · simpa [runningOutputData, hSource, RunningData.sourceState] using facts.trades32
  · simpa [runningOutputData, hSource, RunningData.sourceState] using facts.tradesCapacity
  · have := facts.budget
    change running.g0.toNat ≤ ctx.limit
    omega

#print axioms of_output
end Project.ClobLimit.HeapResidualFacts
