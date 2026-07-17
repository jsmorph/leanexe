import Project.ClobMatchFuel.LoopBranches

/-!
# Match-loop dispatcher composition

The generated dispatcher uses three nested zero-arity branch continuations.
The continuation lemma below reduces their common fallthrough case to the
ordinary program suffix.  The dispatcher theorem then preserves the complete
loop invariant across every source branch.
-/

namespace Project.ClobMatchFuel.LoopIteration

open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobMatchFuel
  Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.LoopBounds

theorem dispatchBranchPost_of_wp (env : HostEnv Unit) (st : Store Unit)
    (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : s.values = []) (hDone : wp «module» rest Q st s env) :
    wp «module» [] (Iteration.dispatchBranchPost env rest Q) st s env := by
  have hBase : { s with values := [] } = s := by
    cases s
    simp_all
  simpa [Iteration.dispatchBranchPost, Iteration.zeroIffPost, wp_simp, hBase]
    using hDone

set_option Elab.async false in
theorem dispatch_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (hFuel : data.fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, Invariant ctx st1 s1 →
      measure st1 s1 < measure st base →
      wp «module» rest Q st1 s1 env) :
    wp «module» (Iteration.dispatchProg ++ rest) Q st base env := by
  rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
    hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTrades, hRemaining,
    hOldBook, hOldTrades, hRunning, hScratch⟩
  have hLength32 : data.orders.length < 4294967296 := by
    have h := facts.book32
    unfold fixedArrayBytes at h
    omega
  have bounds := LoopBounds.of_running ctx st base data facts hFuel
  apply Iteration.dispatchProg_spec env st base data.fuel data.bookOwner data.book
    data.trades data.remaining ctx.taker data.orders hParams hLocals hValues
    hFuelLocal hOid hTrader hSide hPrice hQty hBookOwner hBook hTrades hRemaining
    hLength32 facts.bookOwned.2
  · intro s1 hStop hResult hFuelResult
    have hCompleted :=
      LoopCompletion.of_stop ctx st base data facts hFuel hStop s1 hResult
        hFuelResult
    apply hDone st s1 (Or.inr hCompleted)
    rw [measure_completed hCompleted, measure_running facts]
    omega
  · intro i hRemainingNonzero hFind hMakerQty
    simpa using LoopBranches.full_spec env ctx st base data facts bounds hFuel i
      hRemainingNonzero hFind hMakerQty
      (Iteration.dispatchBranchPost env rest Q) [] (by
        intro st1 s1 hRunning1 hMeasure
        apply dispatchBranchPost_of_wp env st1 s1 rest Q hRunning1.values
        exact hDone st1 s1 (Or.inl hRunning1) hMeasure)
  · intro i hRemainingNonzero hFind hMakerQty
    simpa using LoopBranches.partial_spec env ctx st base data facts bounds hFuel i
      hRemainingNonzero hFind hMakerQty
      (Iteration.dispatchBranchPost env rest Q) [] (by
        intro st1 s1 hCompleted1 hMeasure
        apply dispatchBranchPost_of_wp env st1 s1 rest Q hCompleted1.values
        exact hDone st1 s1 (Or.inr hCompleted1) hMeasure)

end Project.ClobMatchFuel.LoopIteration
