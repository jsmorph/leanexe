import Project.ClobLimit.MatchInvariant
import Project.ClobMatchFuel.LoopIteration

namespace Project.ClobLimit.MatchIteration
open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobMatchFuel
  Project.ClobLimit.MatchInvariant

private abbrev sourceModule := Project.ClobMatchFuel.«module»

set_option Elab.async false in
theorem dispatch_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData) (owner : UInt64)
    (facts : RunningFacts ctx st base data owner) (hFuel : data.fuel ≠ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, Invariant ctx st1 s1 →
      LoopInvariant.measure st1 s1 < LoopInvariant.measure st base →
      wp sourceModule rest Q st1 s1 env) :
    wp sourceModule (MatchDispatch.dispatchProg ++ rest) Q st base env := by
  rcases facts.base.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
    hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTrades, hRemaining,
    hOldBook, hOldTrades, hRunning, hScratch⟩
  have hLength32 : data.orders.length < 4294967296 := by
    have h := facts.base.book32
    unfold fixedArrayBytes at h
    omega
  have bounds := LoopBounds.of_running ctx.base st base data facts.base hFuel
  apply MatchDispatch.dispatchProg_spec env st base data.fuel data.bookOwner
    data.book owner data.trades data.remaining ctx.base.taker data.orders
    hParams hLocals hValues hFuelLocal hOid hTrader hSide hPrice hQty
    hBookOwner hBook facts.owner hTrades hRemaining hLength32 facts.base.bookOwned.2
  · intro s1 hStop hResult hFuelResult
    rcases hResult with ⟨hOwnerBook, hResultBook, hOwnerTrades, hResultTrades,
      hResultRemaining, hResultDone, hResultParams, hResultLocals, hResultValues⟩
    have hCommonResult : LoopControl.CompletedResultAt s1 data.book data.trades
        data.remaining := by
      refine ⟨?_, ?_, ?_, ?_, hResultParams, hResultLocals, hResultValues⟩
      · simpa [Locals.get, hResultParams, hResultLocals] using hResultBook
      · simpa [Locals.get, hResultParams, hResultLocals] using hResultTrades
      · simpa [Locals.get, hResultParams, hResultLocals] using hResultRemaining
      · simpa [Locals.get, hResultParams, hResultLocals] using hResultDone
    have hCommon := LoopCompletion.of_stop ctx.base st base data facts.base
      hFuel hStop s1 hCommonResult hFuelResult
    have hCompleted : CompletedAt ctx st s1 :=
      ⟨_, data.bookOwner, owner, {
        base := hCommon
        bookOwner := hOwnerBook
        tradesOwner := hOwnerTrades
        heapMono := facts.heapMono
        memoryBelow := facts.memoryBelow
        nodesAbove := facts.nodesAbove }⟩
    apply hDone st s1 (Or.inr hCompleted)
    rw [LoopInvariant.measure_completed ⟨_, hCommon⟩,
      LoopInvariant.measure_running facts.base]
    omega
  · intro i hRemainingNonzero hFind hMakerQty
    simpa using LoopBranches.full_spec env ctx.base st base data facts.base bounds
      hFuel i hRemainingNonzero hFind hMakerQty
      (Iteration.dispatchBranchPost env rest Q) [] (by
        intro st1 s1 next hNext hMeasure hHeap hOwner hEffect
        obtain ⟨hMemory, hRoots, hNodes⟩ := hEffect ctx.floor facts.floor48
          facts.heapMono facts.nodesAbove facts.trackedAbove
        have hNextFacts : RunningFacts ctx st1 s1 next next.trades := {
          base := hNext
          owner := hOwner
          floor48 := facts.floor48
          heapMono := facts.heapMono.trans hHeap
          memoryBelow := facts.memoryBelow.trans hMemory
          nodesAbove := hNodes
          trackedAbove := fun _ => hRoots next.trades (by simp) }
        have hRunning : RunningAt ctx st1 s1 := ⟨next, next.trades, hNextFacts⟩
        apply LoopIteration.dispatchBranchPost_of_wp env st1 s1 rest Q hRunning.values
        exact hDone st1 s1 (Or.inl hRunning) hMeasure)
  · intro i hRemainingNonzero hFind hMakerQty
    simpa using LoopBranches.partial_spec env ctx.base st base data facts.base bounds
      hFuel i hRemainingNonzero hFind hMakerQty
      (Iteration.dispatchBranchPost env rest Q) [] (by
        intro st1 s1 next hNext hMeasure hHeap hOwnerBook hOwnerTrades hEffect
        obtain ⟨hMemory, _, hNodes⟩ := hEffect ctx.floor facts.floor48
          facts.heapMono facts.nodesAbove
        have hCompleted : CompletedAt ctx st1 s1 :=
          ⟨next, next.book, next.trades, {
            base := hNext
            bookOwner := hOwnerBook
            tradesOwner := hOwnerTrades
            heapMono := facts.heapMono.trans hHeap
            memoryBelow := facts.memoryBelow.trans hMemory
            nodesAbove := hNodes }⟩
        apply LoopIteration.dispatchBranchPost_of_wp env st1 s1 rest Q hCompleted.values
        exact hDone st1 s1 (Or.inr hCompleted) hMeasure)

#print axioms dispatch_spec
end Project.ClobLimit.MatchIteration
