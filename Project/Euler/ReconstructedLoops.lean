import Project.Euler.ReconstructedSteps
import Project.Euler.ReconstructedSpec

/-! The compiled functions of the reconstructed Euler solver that pass grids by moves compute
their Lean definitions. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

def reconstructedFinishTuple : UInt64 × UInt64 × Float × Moved (Array Cell) → Array Cell :=
  fun (n, trials, ratio, middle) => reconstructedFinish n trials ratio middle.val

theorem reconstructedFinish_implements : Implements euler.module 45 reconstructedFinishTuple := by
  refine Func.implements_moves euler.funcs 43 euler.reconstructedFinish.ir "reconstructedFinish"
    rfl reconstructedFinishTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, trials, ratio, ⟨middle⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hMid⟩ - hCap
  change heap.Owned initial p (flatWords middle) at hMid
  have hLive := Live.start_moved hHeap (temps := [(p, flatWords middle)])
    (by simpa using hMid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values ratio ++ [.i64 p])))
      ((n, trials, ratio, ⟨middle⟩) : UInt64 × UInt64 × Float × Moved (Array Cell)) = [p] := rfl
  rw [hMoves]
  set start := euler.reconstructedFinish.ir.state (Scalar.values n ++ (Scalar.values trials ++
    (Scalar.values ratio ++ [.i64 p]))) with hStartDef
  have hStart : start.params.length + start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 ratio.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 p) := rfl
  let after := start.update 5 (.i64 (if accepted middle then 1 else 0))
  show Triple _ (.seq (.call 12 [⟨.u64, .get 3⟩] [5]) _) 6 _ _
  refine Live.callScalar_seq accepted_implements rfl rfl rfl hLive hCap (x := middle)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet3])
    ⟨p, rfl, hMid.borrowed⟩
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  intro heap1 s1 hLive1
  refine Stmt.ite_test (b := accepted middle)
    (by cases h : accepted middle <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · refine Live.callOne_seq reconstructedSweep_implements rfl rfl rfl (consumed := []) hLive1 hCap
      (x := (n, true, trials, ratio, middle))
      (vals := [.i64 n, .i64 1, .i64 trials, .f64 ratio.toBits, .i64 p])
      (before := after) (afterArgs := after)
      (by simp [Expr.evalResults, Expr.eval, after, hGet0, hGet1, hGet2, hGet3])
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl,
        (hLive1.tempsOwned (p, flatWords middle) (by simp)).borrowed⟩ rfl
      (fun _ _ _ h => nomatch h)
      (fun q => ⟨after.update 4 (.i64 q), by
        simp [State.setAll, State.set?_eq_update, after, hStart]⟩) ?_
    intro heap2 ptr s2 st2 hLive2 hst2
    have hst : st2 = after.update 4 (.i64 ptr) := by
      simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
      exact hst2.symm
    subst hst
    have hy : reconstructedFinishTuple (n, trials, ratio, ⟨middle⟩) =
        reconstructedSweepTuple (n, true, trials, ratio, middle) := by
      simp [reconstructedFinishTuple, reconstructedFinish, hA, reconstructedSweepTuple]
    rw [hy]
    exact Live.releaseSecond_last hLive2 rfl rfl (by simp [after, hGet3]) fun s hL =>
      Live.finish_results_one hL ⟨after.update 4 (.i64 ptr), by
        simp [euler.reconstructedFinish.ir, Expr.evalResults, Expr.eval, after, hStart]⟩
  · have hy : reconstructedFinishTuple (n, trials, ratio, ⟨middle⟩) = middle := by
      simp [reconstructedFinishTuple, reconstructedFinish, hA]
    rw [hy]
    refine Stmt.run_triple ⟨after.update 4 (.i64 p), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet3], ?_⟩
    exact Live.finish_results_one hLive1 ⟨after.update 4 (.i64 p), by
      simp [euler.reconstructedFinish.ir, Expr.evalResults, Expr.eval, after, hStart]⟩

def reconstructedStepGridTuple : UInt64 × UInt64 × Float × Array Cell → Array Cell :=
  fun (n, trials, ratio, grid) => reconstructedStepGrid n trials ratio grid

theorem reconstructedStepGrid_implements :
    Implements euler.module 46 reconstructedStepGridTuple := by
  refine Func.implements_heap euler.funcs 44 euler.reconstructedStepGrid.ir
    "reconstructedStepGrid" rfl reconstructedStepGridTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, trials, ratio, grid⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ hCap
  change heap.Borrowed initial p (flatWords grid) at hGrid
  set start := euler.reconstructedStepGrid.ir.state (Scalar.values n ++ (Scalar.values trials ++
    (Scalar.values ratio ++ [.i64 p]))) with hStartDef
  have hStart : start.params.length + start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 ratio.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 p) := rfl
  show Triple _ (.seq (.call 44 _ [4]) (.call 45 _ [5])) 6 _ _
  refine Live.callOne_seq reconstructedSweep_implements rfl rfl rfl (consumed := [])
    (Live.start hHeap) hCap (x := (n, false, trials, ratio, grid))
    (vals := [.i64 n, .i64 0, .i64 trials, .f64 ratio.toBits, .i64 p]) (before := start)
    (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2, hGet3])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1
  have hst : st1 = start.update 4 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let after := start.update 4 (.i64 ptr)
  refine (Live.callOne reconstructedFinish_implements rfl rfl rfl (consumed := [(ptr, _)])
    (rest := []) hLive1 hCap
    (x := (n, trials, ratio, ⟨reconstructedSweep n false trials ratio grid⟩))
    (vals := [.i64 n, .i64 trials, .f64 ratio.toBits, .i64 ptr]) (before := after)
    (afterArgs := after)
    (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1, hGet2])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl,
      hLive1.tempsOwned _ (List.mem_singleton_self _)⟩
    rfl (fun _ h => by simp [Represent.reads] at h)
    (fun q => ⟨after.update 5 (.i64 q), by simp [State.setAll, State.set?_eq_update, after,
      hStart]⟩)).mono (fun _ _ h => h) ?_
  rintro s st ⟨heap2, ptr2, hLive2, hst2⟩
  have hst : st = after.update 5 (.i64 ptr2) := by
    simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
    exact hst2.symm
  subst hst
  exact Live.finish_results_one (y := reconstructedStepGridTuple (n, trials, ratio, grid)) hLive2
    ⟨after.update 5 (.i64 ptr2), by simp [euler.reconstructedStepGrid.ir, Expr.evalResults,
      Expr.eval, after, hStart]⟩

def reconstructedTryTuple : UInt64 × UInt64 × Array Cell × Float × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, trials, grid, ratio, dt, old) => reconstructedTry n trials grid ratio dt old.val

set_option maxHeartbeats 2000000 in
theorem reconstructedTry_implements : Implements euler.module 50 reconstructedTryTuple := by
  refine Func.implements_moves euler.funcs 48 euler.reconstructedTry.ir "reconstructedTry" rfl
    reconstructedTryTuple
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, rfl, _,
        _, rfl, rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, trials, grid, ratio, dt, ⟨old⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, _, _, rfl, rfl, _, _, rfl,
      rfl, pOld, rfl, hOld⟩ hSep hCap
  change heap.Borrowed initial pGrid (flatWords grid) at hGrid
  change heap.Owned initial pOld (flatWords old) at hOld
  have hLive := Live.start_moved hHeap (temps := [(pOld, flatWords old)])
    (by simpa using hOld) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values trials ++
      ([.i64 pGrid] ++ (Scalar.values ratio ++ (Scalar.values dt ++ [.i64 pOld])))))
      ((n, trials, grid, ratio, dt, ⟨old⟩) :
        UInt64 × UInt64 × Array Cell × Float × Float × Moved (Array Cell)) = [pOld] := rfl
  have hReads : Represent.reads initial (Scalar.values n ++ (Scalar.values trials ++
      ([.i64 pGrid] ++ (Scalar.values ratio ++ (Scalar.values dt ++ [.i64 pOld])))))
      ((n, trials, grid, ratio, dt, ⟨old⟩) :
        UInt64 × UInt64 × Array Cell × Float × Float × Moved (Array Cell)) =
        [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] := rfl
  have hApartGrid : Apart initial [pOld] (pGrid.toNat, 8 * ((flatWords grid).size + 1)) := by
    rw [← hMoves]
    exact hSep.2 _ (by rw [hReads]; exact List.mem_singleton_self _)
  rw [hMoves]
  set start := euler.reconstructedTry.ir.state (Scalar.values n ++ (Scalar.values trials ++
      ([.i64 pGrid] ++ (Scalar.values ratio ++ (Scalar.values dt ++ [.i64 pOld]))))) with hStartDef
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.i64 pGrid) := rfl
  have hGet3 : start.get 3 = some (.f64 ratio.toBits) := rfl
  have hGet4 : start.get 4 = some (.f64 dt.toBits) := rfl
  have hGet5 : start.get 5 = some (.i64 pOld) := rfl
  show Triple _ (.seq (.call 46 _ [6]) (.seq (.call 12 _ [10]) _)) 11 _ _
  refine Live.callOne_seq reconstructedStepGrid_implements rfl rfl rfl (consumed := []) hLive hCap
    (x := (n, trials, ratio, grid))
    (vals := [.i64 n, .i64 trials, .f64 ratio.toBits, .i64 pGrid]) (before := start)
    (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2, hGet3])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
      hLive.borrowed _ _ hGrid (by simpa using hApartGrid)⟩ rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 6 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1
  have hst : st1 = start.update 6 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let trial := reconstructedStepGrid n trials ratio grid
  let after := (start.update 6 (.i64 ptr)).update 10 (.i64 (if accepted trial then 1 else 0))
  refine Live.callScalar_seq accepted_implements rfl rfl rfl hLive1 hCap (x := trial)
    (before := start.update 6 (.i64 ptr)) (afterArgs := start.update 6 (.i64 ptr))
    (after := after) (by simp [Expr.evalResults, Expr.eval, hStart])
    ⟨ptr, rfl, (hLive1.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  intro heap2 s2 hLive2
  refine Stmt.ite_test (b := accepted trial)
    (by cases h : accepted trial <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · have hy : reconstructedTryTuple (n, trials, grid, ratio, dt, ⟨old⟩) =
        (0, dt, reconstructedStepGridTuple (n, trials, ratio, grid)) := by
      simp [reconstructedTryTuple, reconstructedTry, reconstructedStepGridTuple, hA, trial]
    rw [hy]
    let final := ((after.update 7 (.i64 0)).update 8 (.f64 dt.toBits)).update 9 (.i64 ptr)
    refine Stmt.seq_run ⟨after.update 7 (.i64 0), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 7 (.i64 0)).update 8 (.f64 dt.toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet4], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final], ?_⟩
    exact Live.releaseSecond_last hLive2 rfl rfl (by simp [final, after, hGet5]) fun s hL =>
      Live.finish_results_one hL ⟨final, by
        simp [euler.reconstructedTry.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩
  · have hy : reconstructedTryTuple (n, trials, grid, ratio, dt, ⟨old⟩) = (9, 0.5 * dt, old) := by
      simp [reconstructedTryTuple, reconstructedTry, hA, trial]
    rw [hy]
    let final := ((after.update 7 (.i64 9)).update 8 (.f64 (0.5 * dt).toBits)).update 9
      (.i64 pOld)
    refine Stmt.seq_run ⟨after.update 7 (.i64 9), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 7 (.i64 9)).update 8 (.f64 (0.5 * dt).toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet4, F64Op.apply,
        F64Bits.toBits_mul, half_toBits], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final, hGet5], ?_⟩
    exact ((hLive2.releaseFirst rfl rfl (by simp [final, after, hStart])).mono (fun _ _ h => h)
      fun s st ⟨hL, hst⟩ => hst ▸ Live.finish_results_one hL ⟨final, by
        simp [euler.reconstructedTry.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩)

def reconstructedAttemptTuple : UInt64 × UInt64 × Float × Float × Array Cell × Float ×
    Moved (Array Cell) → UInt64 × Float × Array Cell :=
  fun (n, trials, time, alpha, grid, dt, old) =>
    reconstructedAttempt n trials time alpha grid dt old.val

set_option maxHeartbeats 2000000 in
theorem reconstructedAttempt_implements :
    Implements euler.module 51 reconstructedAttemptTuple := by
  refine Func.implements_moves euler.funcs 49 euler.reconstructedAttempt.ir
    "reconstructedAttempt" rfl reconstructedAttemptTuple
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl,
        ⟨_, rfl, -⟩, _, _, rfl, rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, trials, time, alpha, grid, dt, ⟨old⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl,
      ⟨pGrid, rfl, hGrid⟩, _, _, rfl, rfl, pOld, rfl, hOld⟩ hSep hCap
  change heap.Borrowed initial pGrid (flatWords grid) at hGrid
  change heap.Owned initial pOld (flatWords old) at hOld
  have hLive := Live.start_moved hHeap (temps := [(pOld, flatWords old)])
    (by simpa using hOld) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values alpha ++ ([.i64 pGrid] ++ (Scalar.values dt ++
        [.i64 pOld]))))))
      ((n, trials, time, alpha, grid, dt, ⟨old⟩) : UInt64 × UInt64 × Float × Float × Array Cell ×
        Float × Moved (Array Cell)) = [pOld] := rfl
  have hReads : Represent.reads initial (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values alpha ++ ([.i64 pGrid] ++ (Scalar.values dt ++
        [.i64 pOld]))))))
      ((n, trials, time, alpha, grid, dt, ⟨old⟩) : UInt64 × UInt64 × Float × Float × Array Cell ×
        Float × Moved (Array Cell)) = [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] := rfl
  have hApartGrid : Apart initial [pOld] (pGrid.toNat, 8 * ((flatWords grid).size + 1)) := by
    rw [← hMoves]
    exact hSep.2 _ (by rw [hReads]; exact List.mem_singleton_self _)
  rw [hMoves]
  set start := euler.reconstructedAttempt.ir.state (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values alpha ++ ([.i64 pGrid] ++ (Scalar.values dt ++
        [.i64 pOld])))))) with hStartDef
  have hStart : start.params.length + start.locals.length = 12 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 time.toBits) := rfl
  have hGet3 : start.get 3 = some (.f64 alpha.toBits) := rfl
  have hGet4 : start.get 4 = some (.i64 pGrid) := rfl
  have hGet5 : start.get 5 = some (.f64 dt.toBits) := rfl
  have hGet6 : start.get 6 = some (.i64 pOld) := rfl
  let ratio := gridRatio n dt alpha
  let after := (start.update 8 (.f64 ratio.value.toBits)).update 7 (.i64 ratio.status)
  show Triple _ (.seq (.call 49 _ [7, 8]) _) 12 _ _
  refine Stmt.seq_callPure gridRatio_implements rfl rfl rfl (x := (n, dt, alpha)) ⟨start,
    by simp [Expr.evalResults, Expr.eval, hGet0, hGet3, hGet5, Scalar.values], after,
    by simp [State.setAll, State.set?_eq_update, hStart, after, gridRatioTuple, ratio,
      Scalar.values, Flat.flat], ?_⟩
  refine Stmt.ite_test (b := validAdvance time dt)
    (by
      simp [Expr.eval, after, hStart, hGet2, hGet5, U64Op.apply, F64Op.apply, word_and,
        word_beq_one, validAdvance, positive, F64Bits.toBits_add, endTime_toBits,
        Bool.and_assoc])
    (fun hV => ?_) (fun hV => ?_)
  · refine Stmt.ite_test (b := ratio.status == 0) (by simp [Expr.eval, after, hStart])
      (fun hR => ?_) (fun hR => ?_)
    · refine (Live.callOne reconstructedTry_implements rfl rfl rfl (consumed := [(pOld, _)])
        (rest := []) hLive hCap (x := (n, trials, grid, ratio.value, dt, ⟨old⟩))
        (vals := [.i64 n, .i64 trials, .i64 pGrid, .f64 ratio.value.toBits, .f64 dt.toBits,
          .i64 pOld]) (before := after) (afterArgs := after)
        (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1, hGet4, hGet5, hGet6])
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, _, _, rfl, rfl, _, _, rfl,
          rfl, pOld, rfl, hOld⟩
        rfl (fun r hr t ht => by
          rw [List.mem_singleton.mp ht]
          rw [show Represent.reads initial [.i64 n, .i64 trials, .i64 pGrid,
              .f64 ratio.value.toBits, .f64 dt.toBits, .i64 pOld]
              ((n, trials, grid, ratio.value, dt, ⟨old⟩) :
                UInt64 × UInt64 × Array Cell × Float × Float × Moved (Array Cell)) =
              [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] from rfl,
            List.mem_singleton] at hr
          rw [hr]
          exact hApartGrid _ (List.mem_singleton_self _))
        (fun q => ⟨((after.update 11 (.i64 q)).update 10 (.f64 (reconstructedTryTuple
            (n, trials, grid, ratio.value, dt, ⟨old⟩)).2.1.toBits)).update 9
            (.i64 (reconstructedTryTuple (n, trials, grid, ratio.value, dt, ⟨old⟩)).1), by
          simp [State.setAll, State.set?_eq_update, after, hStart, Scalar.values]⟩)).mono
          (fun _ _ h => h) ?_
      rintro s st ⟨heap2, ptr2, hLive2, hst2⟩
      have hy : reconstructedAttemptTuple (n, trials, time, alpha, grid, dt, ⟨old⟩) =
          reconstructedTryTuple (n, trials, grid, ratio.value, dt, ⟨old⟩) := by
        simp only [reconstructedAttemptTuple, reconstructedAttempt, hV, hR, reconstructedTryTuple,
          ite_true, ratio]
      rw [hy]
      exact Live.finish_results_one hLive2 ⟨st, by
        simp [State.setAll, State.set?_eq_update, after, hStart, Scalar.values] at hst2
        simp [euler.reconstructedAttempt.ir, Expr.evalResults, Expr.eval, ← hst2, hStart,
          Scalar.values]⟩
    · have hy : reconstructedAttemptTuple (n, trials, time, alpha, grid, dt, ⟨old⟩) =
          (9, 0.5 * dt, old) := by
        simp only [reconstructedAttemptTuple, reconstructedAttempt, hV, hR, ite_true,
          Bool.false_eq_true, ite_false, ratio]
      rw [hy]
      let final := ((after.update 9 (.i64 9)).update 10 (.f64 (0.5 * dt).toBits)).update 11
        (.i64 pOld)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet5, hGet6, final,
          F64Op.apply, F64Bits.toBits_mul, half_toBits], ?_⟩
      exact Live.finish_results_one hLive ⟨final, by
        simp [euler.reconstructedAttempt.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩
  · have hy : reconstructedAttemptTuple (n, trials, time, alpha, grid, dt, ⟨old⟩) =
        (3, dt, old) := by
      simp only [reconstructedAttemptTuple, reconstructedAttempt, hV, Bool.false_eq_true,
        ite_false]
    rw [hy]
    let final := ((after.update 9 (.i64 3)).update 10 (.f64 dt.toBits)).update 11 (.i64 pOld)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet5, hGet6, final], ?_⟩
    exact Live.finish_results_one hLive ⟨final, by
      simp [euler.reconstructedAttempt.ir, Expr.evalResults, Expr.eval, final, after, hStart,
        Scalar.values]⟩

def reconstructedAdvanceWithTuple : UInt64 × UInt64 × Float × Float × Float ×
    Moved (Array Cell) → UInt64 × Float × Array Cell :=
  fun (n, trials, time, dt, alpha, grid) =>
    reconstructedAdvanceWith n trials time dt alpha grid.val

set_option maxHeartbeats 4000000 in
theorem reconstructedAdvanceWith_implements :
    Implements euler.module 52 reconstructedAdvanceWithTuple := by
  refine Func.implements_moves euler.funcs 50 euler.reconstructedAdvanceWith.ir
    "reconstructedAdvanceWith" rfl reconstructedAdvanceWithTuple
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl,
        rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, trials, time, dt, alpha, ⟨grid⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
      hGrid⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values dt ++ (Scalar.values alpha ++ [.i64 pGrid])))))
      ((n, trials, time, dt, alpha, ⟨grid⟩) :
        UInt64 × UInt64 × Float × Float × Float × Moved (Array Cell)) = [pGrid] := rfl
  rw [hMoves]
  set start := euler.reconstructedAdvanceWith.ir.state (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values dt ++ (Scalar.values alpha ++ [.i64 pGrid])))))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 14 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 time.toBits) := rfl
  have hGet3 : start.get 3 = some (.f64 dt.toBits) := rfl
  have hGet4 : start.get 4 = some (.f64 alpha.toBits) := rfl
  have hGet5 : start.get 5 = some (.i64 pGrid) := rfl
  let s2 := (start.update 6 (.i64 9)).update 7 (.f64 dt.toBits)
  have hS2 : s2.params.length + s2.locals.length = 14 := by simp [s2, hStart]
  show Triple _ (.seq (.assign 6 (.const 9)) (.seq (.assign 7 (.getF 3))
    (.seq (Stmt.arrayLiteral 8 []) (.seq (Stmt.repeatWhile [6, 7, 8] 9 10 (.const 2048)
      ((Expr.get 6).eq (.const 9)) 51 _) _)))) 14 _ _
  refine Stmt.seq_run ⟨start.update 6 (.i64 9), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet3, s2], ?_⟩
  refine Stmt.seq_spec (Stmt.arrayLiteral_spec (values := []) (words := []) rfl rfl rfl
    (by decide) (by omega) hLive.at_ (hLive.cap hCap) (by decide) .nil) ?_
  apply Triple.of_forall
  rintro s3 st3 ⟨pE, hFrame3, hPE, hNew⟩
  have hLive3 := Live.push hLive hNew
  have hT : ∀ j, j < 8 → st3.get j = s2.get j := fun j hj =>
    hFrame3.get j (by omega) (by simp; omega)
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ :=
    reconstructedAdvanceWith_loop n trials time dt alpha grid
  let F : UInt64 × Float × Array Cell → UInt64 × UInt64 × Float × Float × Array Cell × Float ×
      Moved (Array Cell) := fun x => (n, trials, time, alpha, grid, x.2.1, ⟨x.2.2⟩)
  refine Stmt.seq_spec (Live.repeatWhileOne reconstructedAttempt_implements rfl rfl rfl (by decide)
    (by decide) (by rw [hFrame3.params, hFrame3.locals]; omega)
    (n := 2048) ⟨st3, by simp [Expr.eval]⟩ cond step F (fun x => (hStepEq x).symm)
    (x0 := ((9 : UInt64), dt, (#[] : Array Cell))) (p0 := pE) hLive3
    (by
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
      · rw [hT 6 (by decide)]; simp [s2, hStart]
      · rw [hT 7 (by decide)]; simp [s2, hStart]
      · exact hPE)
    hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have h6 : st.get 6 = some (.i64 a) := by
      simp [State.Holds, Scalar.values] at hHolds
      exact hHolds.1
    exact ⟨st, by simp [Expr.eval, h6, hCondEq]⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hFrame
    have hG : ∀ j, j < 6 → st.get j = start.get j := fun j hj =>
      (hFrame.get j (by omega) (by simp; omega)).trans ((hT j (by omega)).trans
        (by simp [s2]; rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]))
    have hH : st.get 6 = some (.i64 a) ∧ st.get 7 = some (.f64 b.toBits) ∧
        st.get 8 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_cons_self ..)
    have hGr : heap'.Owned s pGrid (flatWords grid) :=
      hL.tempsOwned (pGrid, flatWords grid) (by simp)
    have hApart : regionsDisjoint (block s p) (block s pGrid) :=
      (List.pairwise_cons.mp hL.pairwise).1 (pGrid, flatWords grid) (by simp)
    have hF : F (a, b, c) = (n, trials, time, alpha, grid, b, ⟨c⟩) := rfl
    rw [hF]
    have hB : Represent.borrowed heap' s
        [.i64 n, .i64 trials, .f64 time.toBits, .f64 alpha.toBits, .i64 pGrid, .f64 b.toBits,
          .i64 p]
        ((n, trials, time, alpha, grid, b, ⟨c⟩) :
          UInt64 × UInt64 × Float × Float × Array Cell × Float × Moved (Array Cell)) :=
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl,
        ⟨pGrid, rfl, hGr.borrowed⟩, _, _, rfl, rfl, p, rfl, hOld⟩
    have hM : Represent.moves s
        [.i64 n, .i64 trials, .f64 time.toBits, .f64 alpha.toBits, .i64 pGrid, .f64 b.toBits,
          .i64 p]
        ((n, trials, time, alpha, grid, b, ⟨c⟩) :
          UInt64 × UInt64 × Float × Float × Array Cell × Float × Moved (Array Cell)) = [p] := rfl
    refine ⟨[.i64 n, .i64 trials, .f64 time.toBits, .f64 alpha.toBits, .i64 pGrid, .f64 b.toBits,
      .i64 p], st, ?_, hB, hM, fun q hq => ?_⟩
    · simp [Expr.evalResults, Expr.eval, hG 0 (by decide), hG 1 (by decide), hG 2 (by decide),
        hG 4 (by decide), hG 5 (by decide), hH.1, hH.2.1, hH.2.2, hGet0, hGet1, hGet2, hGet4,
        hGet5]
    · rw [show Represent.reads s [.i64 n, .i64 trials, .f64 time.toBits, .f64 alpha.toBits,
          .i64 pGrid, .f64 b.toBits, .i64 p] ((n, trials, time, alpha, grid, b, ⟨c⟩) :
            UInt64 × UInt64 × Float × Float × Array Cell × Float × Moved (Array Cell)) =
            [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] from rfl,
        List.mem_singleton] at hq
      rw [hq]
      exact hGr.region_apart (regionsDisjoint_symm hApart)
  · apply Triple.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4⟩
    generalize hR : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, (#[] : Array Cell)) cond step = R
      at hL4 hHolds4
    obtain ⟨a, b, c⟩ := R
    have hy : reconstructedAdvanceWithTuple (n, trials, time, dt, alpha, ⟨grid⟩) =
        (if a == 0 then ((0 : UInt64), time + b, c)
        else (if a == 9 then 4 else a, time, grid)) := by
      show reconstructedAdvanceWith n trials time dt alpha grid = _
      rw [hDef, hR]
    rw [hy]
    have hLen4 : st4.params.length + st4.locals.length = 14 := by
      rw [hFrame4.params, hFrame4.locals, hFrame3.params, hFrame3.locals]; exact hS2
    have hG : ∀ j, j < 6 → st4.get j = start.get j := fun j hj =>
      (hFrame4.get j (by omega) (by simp; omega)).trans ((hT j (by omega)).trans
        (by simp [s2]; rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]))
    have hH : st4.get 6 = some (.i64 a) ∧ st4.get 7 = some (.f64 b.toBits) ∧
        st4.get 8 = some (.i64 p4) := by
      simpa [State.Holds, Scalar.values] using hHolds4
    refine Stmt.ite_test (b := a == 0) (by simp [Expr.eval, hH.1]) (fun hA => ?_) (fun hA => ?_)
    · simp only [hA, ite_true]
      let final := ((st4.update 11 (.i64 0)).update 12 (.f64 (time + b).toBits)).update 13
        (.i64 p4)
      refine Stmt.seq_run ⟨st4.update 11 (.i64 0), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4], ?_⟩
      refine Stmt.seq_run ⟨(st4.update 11 (.i64 0)).update 12 (.f64 (time + b).toBits), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 2 (by decide), hGet2, hH.2.1,
          F64Op.apply, F64Bits.toBits_add], ?_⟩
      refine Stmt.seq_run ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.2, final], ?_⟩
      exact Live.releaseSecond_last hL4 rfl rfl
        (by simp [final, hG 5 (by decide), hGet5]) fun s hL =>
        Live.finish_results_one hL ⟨final, by
          simp [euler.reconstructedAdvanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4,
            Scalar.values]⟩
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 11 (.i64 (if a == 9 then 4 else a))).update 12
        (.f64 time.toBits)).update 13 (.i64 pGrid)
      refine Stmt.seq_run ⟨st4.update 11 (.i64 (if a == 9 then 4 else a)), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1], ?_⟩
      refine Stmt.seq_run ⟨(st4.update 11 (.i64 (if a == 9 then 4 else a))).update 12
          (.f64 time.toBits), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 2 (by decide), hGet2], ?_⟩
      refine Stmt.seq_run ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 5 (by decide), hGet5,
          final], ?_⟩
      exact ((hL4.releaseFirst rfl rfl (by simp [final, hH.2.2])).mono (fun _ _ h => h)
        fun s st ⟨hL, hst⟩ => hst ▸ Live.finish_results_one hL ⟨final, by
          simp [euler.reconstructedAdvanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4,
            Scalar.values]⟩)

def reconstructedAdvanceStepTuple : UInt64 × UInt64 × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, trials, time, grid) => reconstructedAdvanceStep n trials time grid.val

set_option maxHeartbeats 4000000 in
theorem reconstructedAdvanceStep_implements :
    Implements euler.module 53 reconstructedAdvanceStepTuple := by
  refine Func.implements_moves euler.funcs 51 euler.reconstructedAdvanceStep.ir
    "reconstructedAdvanceStep" rfl reconstructedAdvanceStepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, trials, time, ⟨grid⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl, hGrid⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial
      (Scalar.values n ++ (Scalar.values trials ++ (Scalar.values time ++ [.i64 pGrid])))
      ((n, trials, time, ⟨grid⟩) : UInt64 × UInt64 × Float × Moved (Array Cell)) = [pGrid] :=
    rfl
  rw [hMoves]
  set start := euler.reconstructedAdvanceStep.ir.state
    (Scalar.values n ++ (Scalar.values trials ++ (Scalar.values time ++ [.i64 pGrid])))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 time.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 pGrid) := rfl
  let stats := gridUpper grid
  let after := (start.update 5 (.f64 stats.value.toBits)).update 4 (.i64 stats.status)
  show Triple _ (.seq (.call 48 [⟨.u64, .get 3⟩] [4, 5]) _) 11 _ _
  refine Live.callScalar_seq gridUpper_implements rfl rfl rfl hLive hCap (x := grid)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet3])
    ⟨pGrid, rfl, (hLive.tempsOwned (pGrid, flatWords grid) (by simp)).borrowed⟩
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat,
      stats]) ?_
  intro heap1 s1 hLive1
  refine Stmt.ite_test (b := stats.status == 0) (by simp [Expr.eval, after, hStart])
    (fun hS => ?_) (fun hS => ?_)
  · let a := 0.4 * spacing n / stats.value
    let b := endTime - time
    have hy : reconstructedAdvanceStepTuple (n, trials, time, ⟨grid⟩) =
        reconstructedAdvanceWithTuple (n, trials, time, proposal n time stats.value, stats.value,
          ⟨grid⟩) := by
      simp only [reconstructedAdvanceStepTuple, reconstructedAdvanceStep,
        reconstructedAdvanceWithTuple, hS, ite_true, stats]
    rw [hy]
    let s9 := after.update 9 (.f64 a.toBits)
    let s10 := s9.update 10 (.f64 b.toBits)
    refine Stmt.seq_run ⟨s9, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, after, s9, a, hGet0, F64Op.apply,
        F64Bits.toBits_div, F64Bits.toBits_mul, one_toBits, twoFifths_toBits,
        F64Convert.toBits_toFloat], ?_⟩
    refine Stmt.seq_run ⟨s10, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, after, s9, s10, b, hGet2,
        F64Op.apply, F64Bits.toBits_sub, endTime_toBits], ?_⟩
    refine (Live.callOne reconstructedAdvanceWith_implements rfl rfl rfl
      (consumed := [(pGrid, _)]) (rest := []) hLive1 hCap
      (x := (n, trials, time, proposal n time stats.value, stats.value, ⟨grid⟩))
      (vals := [.i64 n, .i64 trials, .f64 time.toBits, .f64 (proposal n time stats.value).toBits,
        .f64 stats.value.toBits, .i64 pGrid])
      (before := s10) (afterArgs := s10)
      (by
        by_cases hc : a.toBits ≤ b.toBits
        · simp [Expr.evalResults, Expr.eval, s10, s9, after, hStart, hGet0, hGet1, hGet2,
            hGet3, proposal, hc, a, b]
        · simp [Expr.evalResults, Expr.eval, s10, s9, after, hStart, hGet0, hGet1, hGet2,
            hGet3, proposal, hc, a, b])
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
        hLive1.tempsOwned (pGrid, flatWords grid) (by simp)⟩
      rfl (fun r hr => by simp [Represent.reads] at hr)
      (fun q => ⟨((s10.update 8 (.i64 q)).update 7
          (.f64 (reconstructedAdvanceWithTuple (n, trials, time, proposal n time stats.value,
            stats.value, ⟨grid⟩)).2.1.toBits)).update 6
          (.i64 (reconstructedAdvanceWithTuple (n, trials, time, proposal n time stats.value,
            stats.value, ⟨grid⟩)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, s10, s9, after, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2⟩
    exact Live.finish_results_one hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, s10, s9, after, Scalar.values] at hst2
      simp [euler.reconstructedAdvanceStep.ir, Expr.evalResults, Expr.eval, ← hst2, hStart, Scalar.values]⟩
  · have hy : reconstructedAdvanceStepTuple (n, trials, time, ⟨grid⟩) = (2, time, grid) := by
      simp only [reconstructedAdvanceStepTuple, reconstructedAdvanceStep, hS, Bool.false_eq_true,
        ite_false, stats]
    rw [hy]
    let final := ((after.update 6 (.i64 2)).update 7 (.f64 time.toBits)).update 8 (.i64 pGrid)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, after, hGet2, hGet3, final], ?_⟩
    exact Live.finish_results_one hLive1 ⟨final, by
      simp [euler.reconstructedAdvanceStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
        Scalar.values]⟩

def reconstructedRunFromTuple : UInt64 × UInt64 → UInt64 × Float × Array Cell :=
  fun (n, trials) => reconstructedRunFrom n trials

def reconstructedRunTuple : UInt64 × UInt64 → UInt64 × Float × Array Cell :=
  fun (n, trials) => reconstructedRun n trials

def reconstructedSolveTuple : UInt64 × UInt64 → Array UInt64 :=
  fun (n, trials) => reconstructedSolve n trials

set_option maxHeartbeats 4000000 in
theorem reconstructedRunFrom_implements :
    Implements euler.module 54 reconstructedRunFromTuple := by
  refine Func.implements_heap euler.funcs 52 euler.reconstructedRunFrom.ir "reconstructedRunFrom"
    rfl reconstructedRunFromTuple (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨n, trials⟩ heap initial _ hHeap rfl hCap
  set start := euler.reconstructedRunFrom.ir.state (Scalar.values (n, trials)) with hStartDef
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  let s2 := (start.update 2 (.i64 0)).update 3 (.f64 0)
  show Triple _ (.seq (.assign 2 (.const 0)) (.seq (.assign 3 (.constF 0))
    (.seq (.call 10 [⟨.u64, .get 0⟩] [4]) (.seq (Stmt.repeatWhile [2, 3, 4] 5 6
      (.const 4294967296) _ 53 _) _)))) 10 _ _
  refine Stmt.seq_run ⟨start.update 2 (.i64 0), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
  refine Live.callOne_seq initialCells_implements rfl rfl rfl (consumed := []) (Live.start hHeap)
    hCap (x := n) (vals := [.i64 n]) (before := s2) (afterArgs := s2)
    (by simp [Expr.evalResults, Expr.eval, s2, hGet0]) rfl rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨s2.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, s2, hStart]⟩) ?_
  intro heap1 p1 s3 st3 hLive1 hst3
  have hst : st3 = s2.update 4 (.i64 p1) := by
    simp [State.setAll, State.set?_eq_update, s2, hStart] at hst3
    exact hst3.symm
  subst hst
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := reconstructedRunFrom_loop n trials
  let F : UInt64 × Float × Array Cell → UInt64 × UInt64 × Float × Moved (Array Cell) :=
    fun x => (n, trials, x.2.1, ⟨x.2.2⟩)
  have hS3 : (s2.update 4 (.i64 p1)).params.length + (s2.update 4 (.i64 p1)).locals.length = 10 :=
    by simp [s2, hStart]
  refine Stmt.seq_spec (Live.repeatWhileOne reconstructedAdvanceStep_implements rfl rfl rfl
    (by decide) (by decide) (by omega) (n := 4294967296)
    ⟨s2.update 4 (.i64 p1), by simp [Expr.eval]⟩
    cond step F (fun x => (hStepEq x).symm)
    (x0 := ((0 : UInt64), (0 : Float), initialCells n)) (p0 := p1) hLive1
    (by simp [State.Holds, s2, hStart, Scalar.values, zero_toBits]) hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have hH : st.get 2 = some (.i64 a) ∧ st.get 3 = some (.f64 b.toBits) := by
      simp [State.Holds, Scalar.values] at hHolds
      exact ⟨hHolds.1, hHolds.2.1⟩
    exact ⟨st, by
      simp [Expr.eval, hH.1, hH.2, hCondEq, word_and_not, word_beq_one, endTime_toBits,
        U64Op.apply]
      rw [Bool.eq_iff_iff]
      simp⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hFrame
    have hG0 : st.get 0 = some (.i64 n) :=
      (hFrame.get 0 (by omega) (by simp)).trans (by simp [s2, hGet0])
    have hG1 : st.get 1 = some (.i64 trials) :=
      (hFrame.get 1 (by omega) (by simp)).trans (by simp [s2, hGet1])
    have hH : st.get 2 = some (.i64 a) ∧ st.get 3 = some (.f64 b.toBits) ∧
        st.get 4 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_singleton_self _)
    have hF : F (a, b, c) = (n, trials, b, ⟨c⟩) := rfl
    rw [hF]
    refine ⟨[.i64 n, .i64 trials, .f64 b.toBits, .i64 p], st, ?_,
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOld⟩, rfl,
      fun q hq => by simp [Represent.reads] at hq⟩
    simp [Expr.evalResults, Expr.eval, hG0, hG1, hH.2.1, hH.2.2]
  · apply Triple.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4⟩
    generalize hR : LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n)
      cond step = R at hL4 hHolds4
    obtain ⟨a, b, c⟩ := R
    have hy : reconstructedRunFromTuple (n, trials) =
        (if a == 0 && b.toBits != endTime.toBits then (5, b, c) else (a, b, c)) := by
      show reconstructedRunFrom n trials = _
      rw [hDef, hR]
    rw [hy]
    have hLen4 : st4.params.length + st4.locals.length = 10 := by
      rw [hFrame4.params, hFrame4.locals]; exact hS3
    have hH : st4.get 2 = some (.i64 a) ∧ st4.get 3 = some (.f64 b.toBits) ∧
        st4.get 4 = some (.i64 p4) := by
      simpa [State.Holds, Scalar.values] using hHolds4
    refine Stmt.ite_test (b := a == 0 && b.toBits != endTime.toBits)
      (by
        simp [Expr.eval, hH.1, hH.2.1, word_and_not, word_beq_one, endTime_toBits, U64Op.apply]
        rw [Bool.eq_iff_iff]
        simp)
      (fun hA => ?_) (fun hA => ?_)
    · simp only [hA, ite_true]
      let final := ((st4.update 7 (.i64 5)).update 8 (.f64 b.toBits)).update 9 (.i64 p4)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.1, hH.2.2, final], ?_⟩
      exact Live.finish_results_one (y := ((5 : UInt64), b, c)) hL4 ⟨final, by
        simp [euler.reconstructedRunFrom.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 7 (.i64 a)).update 8 (.f64 b.toBits)).update 9 (.i64 p4)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1, hH.2.1, hH.2.2, final], ?_⟩
      exact Live.finish_results_one hL4 ⟨final, by
        simp [euler.reconstructedRunFrom.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩

set_option maxHeartbeats 2000000 in
theorem reconstructedRun_implements : Implements euler.module 55 reconstructedRunTuple := by
  refine Func.implements_heap euler.funcs 53 euler.reconstructedRun.ir "reconstructedRun" rfl
    reconstructedRunTuple (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨n, trials⟩ heap initial _ hHeap rfl hCap
  set start := euler.reconstructedRun.ir.state (Scalar.values (n, trials)) with hStartDef
  have hStart : start.params.length + start.locals.length = 5 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  show Triple _ (.ite _ (.call 54 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3, 4])
    (.seq (.assign 2 (.const 1)) (.seq (.assign 3 (.constF 0)) (Stmt.arrayLiteral 4 [])))) 5 _ _
  refine Stmt.ite_test (b := 2 ≤ n && n ≤ 800)
    (by simp [Expr.eval, hGet0, word_and, word_beq_one, U64Op.apply]) (fun hN => ?_)
    (fun hN => ?_)
  · have hy : reconstructedRunTuple (n, trials) = reconstructedRunFromTuple (n, trials) := by
      simp [reconstructedRunTuple, reconstructedRun, reconstructedRunFromTuple, hN]
    rw [hy]
    refine (Live.callOne reconstructedRunFrom_implements rfl rfl rfl (consumed := [])
      (Live.start hHeap) hCap (x := (n, trials)) (vals := [.i64 n, .i64 trials])
      (before := start) (afterArgs := start)
      (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1]) rfl rfl (fun _ _ _ h => nomatch h)
      (fun q => ⟨((start.update 4 (.i64 q)).update 3
          (.f64 (reconstructedRunFromTuple (n, trials)).2.1.toBits)).update 2
          (.i64 (reconstructedRunFromTuple (n, trials)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2⟩
    exact Live.finish_results_one hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values] at hst2
      simp [euler.reconstructedRun.ir, Expr.evalResults, Expr.eval, ← hst2, hStart,
        Scalar.values]⟩
  · have hy : reconstructedRunTuple (n, trials) = (1, 0, #[]) := by
      simp [reconstructedRunTuple, reconstructedRun, hN]
    rw [hy]
    let s2 := (start.update 2 (.i64 1)).update 3 (.f64 0)
    refine Stmt.seq_run ⟨start.update 2 (.i64 1), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
    refine Stmt.seq_run ⟨s2, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
    refine (Stmt.arrayLiteral_spec (values := []) (words := []) rfl rfl rfl (by decide)
      (by simp [s2, hStart]) hHeap hCap (by decide) .nil).mono (fun _ _ h => h) ?_
    rintro s st ⟨p, hFrame, hP, hNew⟩
    have hLen : st.params.length + st.locals.length = 5 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, hStart]
    have hG : ∀ j, j < 4 → st.get j = s2.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    exact Live.finish_results_one (y := ((1 : UInt64), (0 : Float), (#[] : Array Cell)))
      (Live.push (Live.start hHeap) hNew) ⟨st, by
        simp [euler.reconstructedRun.ir, Expr.evalResults, Expr.eval, hP, hG 2 (by decide),
          hG 3 (by decide), s2, hStart, Scalar.values, zero_toBits]⟩

set_option maxHeartbeats 2000000 in
theorem reconstructedSolve_implements : Implements euler.module 56 reconstructedSolveTuple := by
  refine Func.implements_heap euler.funcs 54 euler.reconstructedSolve.ir "reconstructedSolve" rfl
    reconstructedSolveTuple (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨n, trials⟩ heap initial _ hHeap rfl hCap
  set start := euler.reconstructedSolve.ir.state (Scalar.values (n, trials)) with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      reconstructedRun n trials = (status, time, grid) := ⟨_, _, _, rfl⟩
  have hy : reconstructedSolveTuple (n, trials) = packTuple (n, status, time, grid) := by
    simp [reconstructedSolveTuple, reconstructedSolve, hRun, packTuple]
  rw [hy]
  show Triple _ (.seq (.call 55 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3, 4])
    (.seq (.call 22 _ [5]) (.seq (.assign 6 (.get 5)) (.call 1 [⟨.u64, .get 4⟩] [])))) 7 _ _
  refine Live.callOne_seq reconstructedRun_implements rfl rfl rfl (consumed := [])
    (Live.start hHeap) hCap (x := (n, trials)) (vals := [.i64 n, .i64 trials]) (before := start)
    (afterArgs := start) (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1]) rfl rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨((start.update 4 (.i64 q)).update 3 (.f64 time.toBits)).update 2 (.i64 status), by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values, reconstructedRunTuple,
        hRun]⟩) ?_
  intro heap1 pg s2 st2 hLive1 hst2
  have hst : st2 = ((start.update 4 (.i64 pg)).update 3 (.f64 time.toBits)).update 2
      (.i64 status) := by
    simp [State.setAll, State.set?_eq_update, hStart, Scalar.values, reconstructedRunTuple,
      hRun] at hst2
    exact hst2.symm
  subst hst
  simp only [reconstructedRunTuple, hRun] at hLive1
  let s3 := ((start.update 4 (.i64 pg)).update 3 (.f64 time.toBits)).update 2 (.i64 status)
  refine Live.callOne_seq pack_implements rfl rfl rfl (consumed := []) hLive1 hCap
    (x := (n, status, time, grid)) (vals := [.i64 n, .i64 status, .f64 time.toBits, .i64 pg])
    (before := s3) (afterArgs := s3)
    (by simp [Expr.evalResults, Expr.eval, hGet0, s3, hStart])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pg, rfl,
      (hLive1.tempsOwned (pg, flatWords grid) (by simp)).borrowed⟩ rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨s3.update 5 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart, s3]⟩) ?_
  intro heap2 pk s4 st4 hLive2 hst4
  have hst : st4 = s3.update 5 (.i64 pk) := by
    simp [State.setAll, State.set?_eq_update, hStart, s3] at hst4
    exact hst4.symm
  subst hst
  let final := (s3.update 5 (.i64 pk)).update 6 (.i64 pk)
  refine Stmt.seq_run ⟨final, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s3, final], ?_⟩
  exact Live.releaseSecond_last hLive2 rfl rfl (by simp [final, s3, hStart]) fun s hL =>
    Live.finish_results_one hL ⟨final, by
      simp [euler.reconstructedSolve.ir, Expr.evalResults, Expr.eval, final, s3, hStart]⟩

end Project.Euler
