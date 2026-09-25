import Project.ClobLimit.MatchFinish
import Project.ClobLimit.MatchOutput

namespace Project.ClobLimit.MatchResult
open Wasm Project.ClobLimit.MatchInvariant Project.ClobLimit.MatchOutput

set_option Elab.async false in
theorem finish_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (source target : Locals) (hRelated : MatchLocals.mapping.Related source target)
    (hExit : ExitAt ctx st source) (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ data final, final.values = outputValues ctx data →
      OutputAt ctx st data → wp «module» rest Q st final env) :
    wp «module» (MatchProgram.finish ++ rest) Q st target env := by
  have hValues : target.values = [] := hRelated.2.2.1.symm.trans hExit.values
  rcases hExit with ⟨data, bookOwner, tradesOwner, facts⟩ |
    ⟨data, tradesOwner, facts, hFuel⟩
  · rcases facts.base.result with ⟨hBook, hTrades, hRemaining, hDoneFlag,
      hParams, hLocals, hSourceValues⟩
    have hBookGet : source.get 21 = some (.i64 data.book) := by
      simpa [Locals.get, hParams, hLocals] using hBook
    have hTradesGet : source.get 22 = some (.i64 data.trades) := by
      simpa [Locals.get, hParams, hLocals] using hTrades
    have hRemainingGet : source.get 23 = some (.i64 ctx.result.remaining) := by
      simpa [Locals.get, hParams, hLocals] using hRemaining
    have hDoneGet : source.get 24 = some (.i64 1) := by
      simpa [Locals.get, hParams, hLocals] using hDoneFlag
    apply MatchFinish.completed_spec env st target bookOwner data.book tradesOwner
      data.trades ctx.result.remaining hValues
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 73 (by decide) facts.bookOwner
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 21 (by decide) hBookGet
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 75 (by decide) facts.tradesOwner
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 22 (by decide) hTradesGet
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 23 (by decide) hRemainingGet
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 24 (by decide) hDoneGet
    · apply hDone (completedOutputData data bookOwner tradesOwner)
      · rfl
      · exact of_completed facts
  · rcases facts.base.locals with ⟨_, _, _, _, _, _, _, _, _, hBookOwner,
      hBook, hTrades, hRemaining, _, _, hRunning, _⟩
    have hSource := facts.base.source
    rw [hFuel] at hSource
    simp only [UInt64.toNat_zero, Project.ClobMatchFuel.Model.matchFuelL] at hSource
    apply MatchFinish.running_spec env st target data.bookOwner data.book tradesOwner
      data.trades data.remaining hRelated.2.1.1 hRelated.2.1.2 hValues
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 14 (by decide) hBookOwner
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 15 (by decide) hBook
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 16 (by decide) facts.owner
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 17 (by decide) hTrades
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 18 (by decide) hRemaining
    · simpa [MatchLocals.rename] using MatchLocals.get hRelated 24 (by decide) hRunning
    · apply hDone (runningOutputData data tradesOwner)
      · simp [MatchFinish.runningFrame, outputValues, runningOutputData,
          hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState]
      · exact of_zero_running facts hFuel

#print axioms finish_spec
end Project.ClobLimit.MatchResult
