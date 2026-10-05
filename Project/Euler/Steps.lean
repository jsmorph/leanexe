import Project.Euler.Loops
import Project.IR.OneArray

/-! The compiled functions of the first-order Euler solver that pass grids by moves compute
their Lean definitions. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

/-- The test of a word that the compiler computes from a proposition. -/
theorem word_beq_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) == 1) = decide p := by
  by_cases hp : p <;> simp [hp]

def finishStepTuple : UInt64 × Float × Moved (Array Cell) → Array Cell :=
  fun (n, ratio, middle) => finishStep n ratio middle.val

theorem finishStep_implements : Implements euler.module 13 finishStepTuple := by
  refine Func.implements_moves euler.funcs 11 euler.finishStep.ir "finishStep" rfl
    finishStepTuple (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, ratio, ⟨middle⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hMid⟩ - hCap
  change heap.Owned initial p (flatWords middle) at hMid
  have hLive := Live.start_moved hHeap (temps := [(p, flatWords middle)])
    (by simpa using hMid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values ratio ++ [.i64 p]))
      ((n, ratio, ⟨middle⟩) : UInt64 × Float × Moved (Array Cell)) = [p] := rfl
  rw [hMoves]
  set start := euler.finishStep.ir.state (Scalar.values n ++ (Scalar.values ratio ++ [.i64 p]))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 5 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.f64 ratio.toBits) := rfl
  have hGet2 : start.get 2 = some (.i64 p) := rfl
  let after := start.update 4 (.i64 (if accepted middle then 1 else 0))
  show Triple _ (.seq (.call 12 [⟨.u64, .get 2⟩] [4]) _) 5 _ _
  refine Live.callScalar_seq accepted_implements rfl rfl rfl hLive hCap (x := middle)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet2])
    ⟨p, rfl, hMid.borrowed⟩
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  intro heap1 s1 hLive1
  refine Stmt.ite_test (b := accepted middle)
    (by cases h : accepted middle <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · refine Live.callOne_seq sweep_implements rfl rfl rfl (consumed := []) hLive1 hCap
      (x := (n, true, ratio, middle)) (vals := [.i64 n, .i64 1, .f64 ratio.toBits, .i64 p])
      (before := after) (afterArgs := after)
      (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1, hGet2])
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl,
        (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩ rfl (fun _ _ _ h => nomatch h)
      (fun q => ⟨after.update 3 (.i64 q), by simp [State.setAll, State.set?_eq_update, after, hStart]⟩)
      ?_
    intro heap2 ptr s2 st2 hLive2 hst2
    have hst : st2 = after.update 3 (.i64 ptr) := by
      simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
      exact hst2.symm
    subst hst
    have hy : finishStepTuple (n, ratio, ⟨middle⟩) = sweepTuple (n, true, ratio, middle) := by
      simp [finishStepTuple, finishStep, hA, sweepTuple]
    rw [hy]
    exact Live.releaseSecond_last hLive2 rfl rfl (by simp [after, hStart, hGet2]) fun s hL =>
      Live.finish_results_one hL ⟨after.update 3 (.i64 ptr), by
        simp [euler.finishStep.ir, Expr.evalResults, Expr.eval, after, hStart]⟩
  · have hy : finishStepTuple (n, ratio, ⟨middle⟩) = middle := by
      simp [finishStepTuple, finishStep, hA]
    rw [hy]
    refine Stmt.run_triple ⟨after.update 3 (.i64 p), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet2], ?_⟩
    exact Live.finish_results_one hLive1 ⟨after.update 3 (.i64 p), by
      simp [euler.finishStep.ir, Expr.evalResults, Expr.eval, after, hStart]⟩

def stepTuple : UInt64 × Float × Array Cell → Array Cell :=
  fun (n, ratio, grid) => step n ratio grid

theorem step_implements : Implements euler.module 14 stepTuple := by
  refine Func.implements_heap euler.funcs 12 euler.step.ir "step" rfl stepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, ratio, grid⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ hCap
  change heap.Borrowed initial p (flatWords grid) at hGrid
  set start := euler.step.ir.state (Scalar.values n ++ (Scalar.values ratio ++ [.i64 p]))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 5 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.f64 ratio.toBits) := rfl
  have hGet2 : start.get 2 = some (.i64 p) := rfl
  show Triple _ (.seq (.call 11 _ [3]) (.call 13 _ [4])) 5 _ _
  refine Live.callOne_seq sweep_implements rfl rfl rfl (consumed := []) (Live.start hHeap) hCap
    (x := (n, false, ratio, grid)) (vals := [.i64 n, .i64 0, .f64 ratio.toBits, .i64 p])
    (before := start) (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 3 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1
  have hst : st1 = start.update 3 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let after := start.update 3 (.i64 ptr)
  refine (Live.callOne finishStep_implements rfl rfl rfl (consumed := [(ptr, _)]) (rest := [])
    hLive1 hCap (x := (n, ratio, ⟨sweep n false ratio grid⟩))
    (vals := [.i64 n, .f64 ratio.toBits, .i64 ptr]) (before := after) (afterArgs := after)
    (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl, hLive1.tempsOwned _ (List.mem_singleton_self _)⟩
    rfl (fun _ h => by simp [Represent.reads] at h)
    (fun q => ⟨after.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, after,
      hStart]⟩)).mono (fun _ _ h => h) ?_
  rintro s st ⟨heap2, ptr2, hLive2, hst2⟩
  have hst : st = after.update 4 (.i64 ptr2) := by
    simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
    exact hst2.symm
  subst hst
  exact Live.finish_results_one (y := stepTuple (n, ratio, grid)) hLive2
    ⟨after.update 4 (.i64 ptr2), by simp [euler.step.ir, Expr.evalResults, Expr.eval, after,
      hStart]⟩

def tryStepTuple : UInt64 × Array Cell × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, grid, dt, old) => tryStep n grid dt old.val

set_option maxHeartbeats 2000000 in
theorem tryStep_implements : Implements euler.module 16 tryStepTuple := by
  refine Func.implements_moves euler.funcs 14 euler.tryStep.ir "tryStep" rfl tryStepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, rfl, _, rfl, -⟩; rfl)
    ?_
  rintro ⟨n, grid, dt, ⟨old⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, _, _, rfl, rfl, pOld, rfl, hOld⟩ hSep hCap
  change heap.Borrowed initial pGrid (flatWords grid) at hGrid
  change heap.Owned initial pOld (flatWords old) at hOld
  have hLive := Live.start_moved hHeap (temps := [(pOld, flatWords old)])
    (by simpa using hOld) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial
      (Scalar.values n ++ ([.i64 pGrid] ++ (Scalar.values dt ++ [.i64 pOld])))
      ((n, grid, dt, ⟨old⟩) : UInt64 × Array Cell × Float × Moved (Array Cell)) = [pOld] := rfl
  have hReads : Represent.reads initial
      (Scalar.values n ++ ([.i64 pGrid] ++ (Scalar.values dt ++ [.i64 pOld])))
      ((n, grid, dt, ⟨old⟩) : UInt64 × Array Cell × Float × Moved (Array Cell)) =
        [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] := rfl
  have hApartGrid : Apart initial [pOld] (pGrid.toNat, 8 * ((flatWords grid).size + 1)) := by
    rw [← hMoves]
    exact hSep.2 _ (by rw [hReads]; exact List.mem_singleton_self _)
  rw [hMoves]
  set start := euler.tryStep.ir.state
    (Scalar.values n ++ ([.i64 pGrid] ++ (Scalar.values dt ++ [.i64 pOld]))) with hStartDef
  have hStart : start.params.length + start.locals.length = 9 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 pGrid) := rfl
  have hGet2 : start.get 2 = some (.f64 dt.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 pOld) := rfl
  show Triple _ (.seq (.call 14 _ [4]) (.seq (.call 12 _ [8]) _)) 9 _ _
  refine Live.callOne_seq step_implements rfl rfl rfl (consumed := []) hLive hCap
    (x := (n, dt / spacing n, grid))
    (vals := [.i64 n, .f64 (dt / spacing n).toBits, .i64 pGrid]) (before := start)
    (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2, F64Op.apply, F64Bits.toBits_div,
      one_toBits, F64Convert.toBits_toFloat])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
      hLive.borrowed _ _ hGrid (by simpa using hApartGrid)⟩ rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1
  have hst : st1 = start.update 4 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let trial := step n (dt / spacing n) grid
  let after := (start.update 4 (.i64 ptr)).update 8 (.i64 (if accepted trial then 1 else 0))
  refine Live.callScalar_seq accepted_implements rfl rfl rfl hLive1 hCap (x := trial)
    (before := start.update 4 (.i64 ptr)) (afterArgs := start.update 4 (.i64 ptr))
    (after := after) (by simp [Expr.evalResults, Expr.eval, hStart])
    ⟨ptr, rfl, (hLive1.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  intro heap2 s2 hLive2
  refine Stmt.ite_test (b := accepted trial)
    (by cases h : accepted trial <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · have hy : tryStepTuple (n, grid, dt, ⟨old⟩) = (0, dt, stepTuple (n, dt / spacing n, grid)) := by
      simp [tryStepTuple, tryStep, stepTuple, hA, trial]
    rw [hy]
    let final := ((after.update 5 (.i64 0)).update 6 (.f64 dt.toBits)).update 7 (.i64 ptr)
    refine Stmt.seq_run ⟨after.update 5 (.i64 0), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 5 (.i64 0)).update 6 (.f64 dt.toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet2], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final], ?_⟩
    exact Live.releaseSecond_last hLive2 rfl rfl (by simp [final, after, hStart, hGet3])
      fun s hL => Live.finish_results_one hL ⟨final, by
        simp [euler.tryStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩
  · have hy : tryStepTuple (n, grid, dt, ⟨old⟩) = (9, 0.5 * dt, old) := by
      simp [tryStepTuple, tryStep, hA, trial]
    rw [hy]
    let final := ((after.update 5 (.i64 9)).update 6 (.f64 (0.5 * dt).toBits)).update 7
      (.i64 pOld)
    refine Stmt.seq_run ⟨after.update 5 (.i64 9), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 5 (.i64 9)).update 6 (.f64 (0.5 * dt).toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet2, F64Op.apply,
        F64Bits.toBits_mul, half_toBits], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final, hGet3], ?_⟩
    exact ((hLive2.releaseFirst rfl rfl (by simp [final, after, hStart])).mono (fun _ _ h => h)
      fun s st ⟨hL, hst⟩ => hst ▸ Live.finish_results_one hL ⟨final, by
        simp [euler.tryStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩)

def attemptTuple : UInt64 × Float × Array Cell × UInt64 × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, time, grid, status, dt, old) => attempt n time grid status dt old.val

set_option maxHeartbeats 2000000 in
theorem attempt_implements : Implements euler.module 17 attemptTuple := by
  refine Func.implements_moves euler.funcs 15 euler.attempt.ir "attempt" rfl attemptTuple
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, rfl, _,
        _, rfl, rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, time, grid, status, dt, ⟨old⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, _, _, rfl, rfl, _, _, rfl,
      rfl, pOld, rfl, hOld⟩ hSep hCap
  change heap.Borrowed initial pGrid (flatWords grid) at hGrid
  change heap.Owned initial pOld (flatWords old) at hOld
  have hLive := Live.start_moved hHeap (temps := [(pOld, flatWords old)])
    (by simpa using hOld) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values time ++
      ([.i64 pGrid] ++ (Scalar.values status ++ (Scalar.values dt ++ [.i64 pOld])))))
      ((n, time, grid, status, dt, ⟨old⟩) :
        UInt64 × Float × Array Cell × UInt64 × Float × Moved (Array Cell)) = [pOld] := rfl
  have hReads : Represent.reads initial (Scalar.values n ++ (Scalar.values time ++
      ([.i64 pGrid] ++ (Scalar.values status ++ (Scalar.values dt ++ [.i64 pOld])))))
      ((n, time, grid, status, dt, ⟨old⟩) :
        UInt64 × Float × Array Cell × UInt64 × Float × Moved (Array Cell)) =
        [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] := rfl
  have hApartGrid : Apart initial [pOld] (pGrid.toNat, 8 * ((flatWords grid).size + 1)) := by
    rw [← hMoves]
    exact hSep.2 _ (by rw [hReads]; exact List.mem_singleton_self _)
  rw [hMoves]
  set start := euler.attempt.ir.state (Scalar.values n ++ (Scalar.values time ++
      ([.i64 pGrid] ++ (Scalar.values status ++ (Scalar.values dt ++ [.i64 pOld]))))) with hStartDef
  have hStart : start.params.length + start.locals.length = 9 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.f64 time.toBits) := rfl
  have hGet2 : start.get 2 = some (.i64 pGrid) := rfl
  have hGet4 : start.get 4 = some (.f64 dt.toBits) := rfl
  have hGet5 : start.get 5 = some (.i64 pOld) := rfl
  show Triple _ (.ite _ _ _) 9 _ _
  refine Stmt.ite_test (b := validAdvance time dt)
    (by
      simp [Expr.eval, hGet1, hGet4, U64Op.apply, F64Op.apply, word_and, word_beq_one,
        validAdvance, positive, F64Bits.toBits_add, endTime_toBits, Bool.and_assoc])
    (fun hV => ?_) (fun hV => ?_)
  · refine (Live.callOne tryStep_implements rfl rfl rfl (consumed := [(pOld, _)]) (rest := [])
      hLive hCap (x := (n, grid, dt, ⟨old⟩))
      (vals := [.i64 n, .i64 pGrid, .f64 dt.toBits, .i64 pOld]) (before := start)
      (afterArgs := start)
      (by simp [Expr.evalResults, Expr.eval, hGet0, hGet2, hGet4, hGet5])
      ⟨_, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, _, _, rfl, rfl, pOld, rfl, hOld⟩
      rfl (fun r hr t ht => by
        rw [List.mem_singleton.mp ht]
        rw [show Represent.reads initial [.i64 n, .i64 pGrid, .f64 dt.toBits, .i64 pOld]
            ((n, grid, dt, ⟨old⟩) : UInt64 × Array Cell × Float × Moved (Array Cell)) =
            [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] from rfl,
          List.mem_singleton] at hr
        rw [hr]
        exact hApartGrid _ (List.mem_singleton_self _))
      (fun q => ⟨((start.update 8 (.i64 q)).update 7
          (.f64 (tryStepTuple (n, grid, dt, ⟨old⟩)).2.1.toBits)).update 6
          (.i64 (tryStepTuple (n, grid, dt, ⟨old⟩)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2⟩
    have hy : attemptTuple (n, time, grid, status, dt, ⟨old⟩) = tryStepTuple (n, grid, dt, ⟨old⟩) := by
      simp only [attemptTuple, attempt, hV, tryStepTuple, ite_true]
    rw [hy]
    exact Live.finish_results_one hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values] at hst2
      simp [euler.attempt.ir, Expr.evalResults, Expr.eval, ← hst2, hStart, Scalar.values]⟩
  · have hy : attemptTuple (n, time, grid, status, dt, ⟨old⟩) = (3, dt, old) := by
      simp only [attemptTuple, attempt, hV, Bool.false_eq_true, ite_false]
    rw [hy]
    let final := ((start.update 6 (.i64 3)).update 7 (.f64 dt.toBits)).update 8 (.i64 pOld)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet4, hGet5, final], ?_⟩
    exact Live.finish_results_one hLive ⟨final, by
      simp [euler.attempt.ir, Expr.evalResults, Expr.eval, final, hStart, Scalar.values]⟩

def advanceWithTuple : UInt64 × Float × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, time, dt, grid) => advanceWith n time dt grid.val

/-- `advanceWith` with its loop's test and step named. -/
theorem advanceWith_loop (n : UInt64) (time dt : Float) (grid : Array Cell) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 9)) ∧ (∀ x, step x = attempt n time grid x.1 x.2.1 x.2.2) ∧
      advanceWith n time dt grid =
        match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, (#[] : Array Cell)) cond step with
        | (status, dt, trial) =>
          if status == 0 then ((0 : UInt64), time + dt, trial)
          else (if status == 9 then 4 else status, time, grid) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

set_option maxHeartbeats 4000000 in
theorem advanceWith_implements : Implements euler.module 18 advanceWithTuple := by
  refine Func.implements_moves euler.funcs 16 euler.advanceWith.ir "advanceWith" rfl
    advanceWithTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, time, dt, ⟨grid⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl, hGrid⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial
      (Scalar.values n ++ (Scalar.values time ++ (Scalar.values dt ++ [.i64 pGrid])))
      ((n, time, dt, ⟨grid⟩) : UInt64 × Float × Float × Moved (Array Cell)) = [pGrid] := rfl
  rw [hMoves]
  set start := euler.advanceWith.ir.state
    (Scalar.values n ++ (Scalar.values time ++ (Scalar.values dt ++ [.i64 pGrid])))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 12 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.f64 time.toBits) := rfl
  have hGet2 : start.get 2 = some (.f64 dt.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 pGrid) := rfl
  let s2 := (start.update 4 (.i64 9)).update 5 (.f64 dt.toBits)
  have hS2 : s2.params.length + s2.locals.length = 12 := by simp [s2, hStart]
  show Triple _ (.seq (.assign 4 (.const 9)) (.seq (.assign 5 (.getF 2))
    (.seq (Stmt.arrayLiteral 6 []) (.seq (Stmt.repeatWhile [4, 5, 6] 7 8 (.const 2048)
      ((Expr.get 4).eq (.const 9)) 17 _) _)))) 12 _ _
  refine Stmt.seq_run ⟨start.update 4 (.i64 9), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet2, s2], ?_⟩
  refine Stmt.seq_spec (Stmt.arrayLiteral_spec (values := []) (words := []) rfl rfl rfl
    (by decide) (by omega) hLive.at_ (hLive.cap hCap) (by decide) .nil) ?_
  apply Triple.of_forall
  rintro s3 st3 ⟨pE, hFrame3, hPE, hNew⟩
  have hLive3 := Live.push hLive hNew
  have hT : ∀ j, j < 6 → st3.get j = s2.get j := fun j hj =>
    hFrame3.get j (by omega) (by simp; omega)
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := advanceWith_loop n time dt grid
  let F : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell × UInt64 × Float ×
      Moved (Array Cell) := fun x => (n, time, grid, x.1, x.2.1, ⟨x.2.2⟩)
  refine Stmt.seq_spec (Live.repeatWhileOne attempt_implements rfl rfl rfl (by decide)
    (by decide) (by rw [hFrame3.params, hFrame3.locals]; omega)
    (n := 2048) ⟨st3, by simp [Expr.eval]⟩ cond step F (fun x => (hStepEq x).symm)
    (x0 := ((9 : UInt64), dt, (#[] : Array Cell))) (p0 := pE) hLive3
    (by
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
      · rw [hT 4 (by decide)]; simp [s2, hStart]
      · rw [hT 5 (by decide)]; simp [s2, hStart, Scalar.values]
      · exact hPE)
    hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have h4 : st.get 4 = some (.i64 a) := by
      simp [State.Holds, Scalar.values] at hHolds
      exact hHolds.1
    exact ⟨st, by simp [Expr.eval, h4, hCondEq]⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hFrame
    have hG : ∀ j, j < 4 → st.get j = start.get j := fun j hj =>
      (hFrame.get j (by omega) (by simp; omega)).trans ((hT j (by omega)).trans
        (by simp [s2]; rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]))
    have hH : st.get 4 = some (.i64 a) ∧ st.get 5 = some (.f64 b.toBits) ∧
        st.get 6 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_cons_self ..)
    have hGr : heap'.Owned s pGrid (flatWords grid) :=
      hL.tempsOwned (pGrid, flatWords grid) (by simp)
    have hApart : regionsDisjoint (block s p) (block s pGrid) :=
      (List.pairwise_cons.mp hL.pairwise).1 (pGrid, flatWords grid) (by simp)
    have hF : F (a, b, c) = (n, time, grid, a, b, ⟨c⟩) := rfl
    rw [hF]
    have hB : Represent.borrowed heap' s
        [.i64 n, .f64 time.toBits, .i64 pGrid, .i64 a, .f64 b.toBits, .i64 p]
        ((n, time, grid, a, b, ⟨c⟩) :
          UInt64 × Float × Array Cell × UInt64 × Float × Moved (Array Cell)) :=
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGr.borrowed⟩, _, _, rfl, rfl, _, _,
        rfl, rfl, p, rfl, hOld⟩
    have hM : Represent.moves s
        [.i64 n, .f64 time.toBits, .i64 pGrid, .i64 a, .f64 b.toBits, .i64 p]
        ((n, time, grid, a, b, ⟨c⟩) :
          UInt64 × Float × Array Cell × UInt64 × Float × Moved (Array Cell)) = [p] := rfl
    refine ⟨[.i64 n, .f64 time.toBits, .i64 pGrid, .i64 a, .f64 b.toBits, .i64 p], st, ?_,
      hB, hM, fun q hq => ?_⟩
    · simp [Expr.evalResults, Expr.eval, hG 0 (by decide), hG 1 (by decide), hG 3 (by decide),
        hH.1, hH.2.1, hH.2.2, hGet0, hGet1, hGet3]
    · rw [show Represent.reads s [.i64 n, .f64 time.toBits, .i64 pGrid, .i64 a, .f64 b.toBits,
          .i64 p] ((n, time, grid, a, b, ⟨c⟩) :
            UInt64 × Float × Array Cell × UInt64 × Float × Moved (Array Cell)) =
            [(pGrid.toNat, 8 * ((flatWords grid).size + 1))] from rfl,
        List.mem_singleton] at hq
      rw [hq]
      exact hGr.region_apart (regionsDisjoint_symm hApart)
  · apply Triple.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4⟩
    generalize hR : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, (#[] : Array Cell)) cond step = R
      at hL4 hHolds4
    obtain ⟨a, b, c⟩ := R
    have hy : advanceWithTuple (n, time, dt, ⟨grid⟩) = (if a == 0 then ((0 : UInt64), time + b, c)
        else (if a == 9 then 4 else a, time, grid)) := by
      show advanceWith n time dt grid = _
      rw [hDef, hR]
    rw [hy]
    have hLen4 : st4.params.length + st4.locals.length = 12 := by
      rw [hFrame4.params, hFrame4.locals, hFrame3.params, hFrame3.locals]; exact hS2
    have hG : ∀ j, j < 4 → st4.get j = start.get j := fun j hj =>
      (hFrame4.get j (by omega) (by simp; omega)).trans ((hT j (by omega)).trans
        (by simp [s2]; rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]))
    have hH : st4.get 4 = some (.i64 a) ∧ st4.get 5 = some (.f64 b.toBits) ∧
        st4.get 6 = some (.i64 p4) := by
      simpa [State.Holds, Scalar.values] using hHolds4
    refine Stmt.ite_test (b := a == 0) (by simp [Expr.eval, hH.1]) (fun hA => ?_) (fun hA => ?_)
    · simp only [hA, ite_true]
      let final := ((st4.update 9 (.i64 0)).update 10 (.f64 (time + b).toBits)).update 11
        (.i64 p4)
      refine Stmt.seq_run ⟨st4.update 9 (.i64 0), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4], ?_⟩
      refine Stmt.seq_run ⟨(st4.update 9 (.i64 0)).update 10 (.f64 (time + b).toBits), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 1 (by decide), hGet1, hH.2.1,
          F64Op.apply, F64Bits.toBits_add], ?_⟩
      refine Stmt.seq_run ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.2, final], ?_⟩
      exact Live.releaseSecond_last hL4 rfl rfl
        (by simp [final, hLen4, hG 3 (by decide), hGet3]) fun s hL =>
        Live.finish_results_one hL ⟨final, by
          simp [euler.advanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 9 (.i64 (if a == 9 then 4 else a))).update 10
        (.f64 time.toBits)).update 11 (.i64 pGrid)
      refine Stmt.seq_run ⟨st4.update 9 (.i64 (if a == 9 then 4 else a)), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1], ?_⟩
      refine Stmt.seq_run ⟨(st4.update 9 (.i64 (if a == 9 then 4 else a))).update 10
          (.f64 time.toBits), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 1 (by decide), hGet1], ?_⟩
      refine Stmt.seq_run ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 3 (by decide), hGet3,
          final], ?_⟩
      exact ((hL4.releaseFirst rfl rfl (by simp [final, hLen4, hH.2.2])).mono (fun _ _ h => h)
        fun s st ⟨hL, hst⟩ => hst ▸ Live.finish_results_one hL ⟨final, by
          simp [euler.advanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4,
            Scalar.values]⟩)

end Project.Euler
