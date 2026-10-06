import Examples.Euler.Loops
import Project.IR.OneArray
import Examples.Euler.Spec

/-! The compiled functions of the first-order Euler solver that pass grids by moves compute
their Lean definitions. -/

namespace Examples.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Euler

def finishStepTuple : UInt64 × Float × Moved (Array Cell) → Array Cell :=
  fun (n, ratio, middle) => finishStep n ratio middle.val

/-- Under `a = false`, the middle grid has `cells` cells, and the heap has room for one more
grid. -/
theorem finishStep_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 13 finishStepTuple
      (fun x heap store => a = false → x.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 1) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final euler.module g (spare + 1) pages) := by
  refine Func.implements_movesA euler.funcs 11 euler.finishStep.ir "finishStep" rfl
    finishStepTuple _ _ (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, ratio, ⟨middle⟩⟩ heap initial _ hHeap hPre
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
  show TripleA _ _ (.seq (.call 12 [⟨.u64, .get 2⟩] [4]) _) 5 _ _
  refine Live.callScalar_seqA accepted_implementsA rfl rfl rfl hLive hCap (x := middle)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet2])
    ⟨p, rfl, hMid.borrowed⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  rintro heap1 s1 hLive1 ⟨rfl, rfl⟩
  refine Stmt.ite_test (b := accepted middle)
    (by cases h : accepted middle <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · refine Live.callOne_seqA (sweep_implementsA hg spare pages) rfl rfl rfl (consumed := [])
      hLive1 hCap (x := (n, true, ratio, middle))
      (vals := [.i64 n, .i64 1, .f64 ratio.toBits, .i64 p]) (before := after) (afterArgs := after)
      (by simp [Expr.evalResults, Expr.eval, after, hGet0, hGet1, hGet2])
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl,
        (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩ hPre rfl
      (fun _ _ _ h => nomatch h)
      (fun q => ⟨after.update 3 (.i64 q), by
        simp [State.setAll, State.set?_eq_update, after, hStart]⟩) ?_
    intro heap2 ptr s2 st2 hLive2 hst2 hPost2
    have hst : st2 = after.update 3 (.i64 ptr) := by
      simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
      exact hst2.symm
    subst hst
    have hy : finishStepTuple (n, ratio, ⟨middle⟩) = sweepTuple (n, true, ratio, middle) := by
      simp [finishStepTuple, finishStep, hA, sweepTuple]
    rw [hy]
    exact Live.releaseSecond_last_pages hLive2 rfl rfl (by simp [after, hGet2])
      fun s hL hPages => Live.finish_results_oneP (P := Spare a g (spare + 1) pages) hL ⟨after.update 3 (.i64 ptr), by
        simp [euler.finishStep.ir, Expr.evalResults, Expr.eval, after, hStart]⟩
        fun ha => (hPost2 ha).release_one hLive2.at_
          (hLive2.tempsOwned (p, flatWords middle) (by simp))
          (by rw [flatWords_size cell_length, (hPre ha).1, hg.bytes]) hPages
          (hL.caps.trans hLive2.caps.symm)
  · have hy : finishStepTuple (n, ratio, ⟨middle⟩) = middle := by
      simp [finishStepTuple, finishStep, hA]
    rw [hy]
    refine Stmt.run_triple ⟨after.update 3 (.i64 p), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet2], ?_⟩
    exact Live.finish_results_oneP (P := Spare a g (spare + 1) pages) hLive1 ⟨after.update 3 (.i64 p), by
      simp [euler.finishStep.ir, Expr.evalResults, Expr.eval, after, hStart]⟩
      fun ha => (hPre ha).2

theorem finishStep_implements : Implements euler.module 13 finishStepTuple :=
  (finishStep_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

def stepTuple : UInt64 × Float × Array Cell → Array Cell :=
  fun (n, ratio, grid) => step n ratio grid

/-- Under `a = false`, the grid has `cells` cells, and the heap has room for two more grids. -/
theorem step_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 14 stepTuple
      (fun x heap store => a = false → x.2.2.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final euler.module g (spare + 1) pages) := by
  refine Func.implements_heapA euler.funcs 12 euler.step.ir "step" rfl stepTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, ratio, grid⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ hCap
  change heap.Borrowed initial p (flatWords grid) at hGrid
  set start := euler.step.ir.state (Scalar.values n ++ (Scalar.values ratio ++ [.i64 p]))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 5 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.f64 ratio.toBits) := rfl
  have hGet2 : start.get 2 = some (.i64 p) := rfl
  show TripleA _ _ (.seq (.call 11 _ [3]) (.call 13 _ [4])) 5 _ _
  refine Live.callOne_seqA (sweep_implementsA hg (spare + 1) pages) rfl rfl rfl (consumed := [])
    (Live.start hHeap) hCap
    (x := (n, false, ratio, grid)) (vals := [.i64 n, .i64 0, .f64 ratio.toBits, .i64 p])
    (before := start) (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ hPre rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 3 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1 hPost1
  have hst : st1 = start.update 3 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let after := start.update 3 (.i64 ptr)
  refine (Live.callOneA (finishStep_implementsA hg spare pages) rfl rfl rfl
    (consumed := [(ptr, _)]) (rest := [])
    hLive1 hCap (x := (n, ratio, ⟨sweep n false ratio grid⟩))
    (vals := [.i64 n, .f64 ratio.toBits, .i64 ptr]) (before := after) (afterArgs := after)
    (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl, hLive1.tempsOwned _ (List.mem_singleton_self _)⟩
    (fun ha => ⟨by
      have := hg.cells
      have : grid.size = cells := (hPre ha).1
      rw [sweep_size _ _ _ _ (by omega)]; exact (hPre ha).1, hPost1 ha⟩)
    rfl (fun _ h => by simp [Represent.reads] at h)
    (fun q => ⟨after.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, after,
      hStart]⟩)).mono (fun _ _ h => h) ?_
  rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
  have hst : st = after.update 4 (.i64 ptr2) := by
    simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
    exact hst2.symm
  subst hst
  exact Live.finish_results_oneP (P := Spare a g (spare + 1) pages) (y := stepTuple (n, ratio, grid)) hLive2
    ⟨after.update 4 (.i64 ptr2), by simp [euler.step.ir, Expr.evalResults, Expr.eval, after,
      hStart]⟩ hPost2

theorem step_implements : Implements euler.module 14 stepTuple :=
  (step_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

def tryStepTuple : UInt64 × Moved (Array Cell) × Float → UInt64 × Float × Array Cell :=
  fun (n, grid, dt) => tryStep n grid.val dt

set_option maxHeartbeats 2000000 in
/-- Under `a = false`, the grid has `cells` cells, and the heap has room for two more grids. -/
theorem tryStep_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 16 tryStepTuple
      (fun x heap store => a = false → x.2.1.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 14 euler.tryStep.ir "tryStep" rfl tryStepTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨n, ⟨grid⟩, dt⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, rfl⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ ([.i64 pGrid] ++ Scalar.values dt))
      ((n, ⟨grid⟩, dt) : UInt64 × Moved (Array Cell) × Float) = [pGrid] := rfl
  rw [hMoves]
  set start := euler.tryStep.ir.state (Scalar.values n ++ ([.i64 pGrid] ++ Scalar.values dt))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 8 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 pGrid) := rfl
  have hGet2 : start.get 2 = some (.f64 dt.toBits) := rfl
  have hSmall := hg.cells
  show TripleA _ _ (.seq (.call 14 _ [3]) (.seq (.call 12 _ [7]) _)) 8 _ _
  refine Live.callOne_seqA (step_implementsA hg spare pages) rfl rfl rfl (consumed := []) hLive
    hCap (x := (n, dt / spacing n, grid))
    (vals := [.i64 n, .f64 (dt / spacing n).toBits, .i64 pGrid]) (before := start)
    (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2, F64Op.apply, F64Bits.toBits_div,
      one_toBits, F64Convert.toBits_toFloat])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
      (hLive.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩ hPre rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 3 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1 hPost1
  have hst : st1 = start.update 3 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let trial := step n (dt / spacing n) grid
  let after := (start.update 3 (.i64 ptr)).update 7 (.i64 (if accepted trial then 1 else 0))
  refine Live.callScalar_seqA accepted_implementsA rfl rfl rfl hLive1 hCap (x := trial)
    (before := start.update 3 (.i64 ptr)) (afterArgs := start.update 3 (.i64 ptr))
    (after := after) (by simp [Expr.evalResults, Expr.eval, hStart])
    ⟨ptr, rfl, (hLive1.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  rintro heap2 s2 hLive2 ⟨rfl, rfl⟩
  have hFit : ∀ (c : Array Cell), c.size = cells → g.toNat ≤ 8 * ((flatWords c).size + 1) :=
    fun c hc => by rw [flatWords_size cell_length, hc, hg.bytes]
  refine Stmt.ite_test (b := accepted trial)
    (by cases h : accepted trial <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · have hy : tryStepTuple (n, ⟨grid⟩, dt) = (0, dt, stepTuple (n, dt / spacing n, grid)) := by
      simp [tryStepTuple, tryStep, stepTuple, hA, trial]
    rw [hy]
    let final := ((after.update 4 (.i64 0)).update 5 (.f64 dt.toBits)).update 6 (.i64 ptr)
    refine Stmt.seq_run ⟨after.update 4 (.i64 0), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 4 (.i64 0)).update 5 (.f64 dt.toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet2], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final], ?_⟩
    exact Live.releaseSecond_last_pages hLive2 rfl rfl (by simp [final, after, hGet1])
      fun s hL hPages => Live.finish_results_oneP (P := Spare a g (spare + 2) pages) hL ⟨final, by
        simp [euler.tryStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩
        fun ha => (hPost1 ha).release_one hLive2.at_
          (hLive2.tempsOwned (pGrid, flatWords grid) (by simp)) (hFit grid (hPre ha).1) hPages
          (hL.caps.trans hLive2.caps.symm)
  · have hy : tryStepTuple (n, ⟨grid⟩, dt) = (9, 0.5 * dt, grid) := by
      simp [tryStepTuple, tryStep, hA, trial]
    rw [hy]
    let final := ((after.update 4 (.i64 9)).update 5 (.f64 (0.5 * dt).toBits)).update 6
      (.i64 pGrid)
    refine Stmt.seq_run ⟨after.update 4 (.i64 9), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 4 (.i64 9)).update 5 (.f64 (0.5 * dt).toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet2, F64Op.apply,
        F64Bits.toBits_mul, half_toBits], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final, hGet1], ?_⟩
    exact ((hLive2.releaseFirst_pages rfl rfl (by simp [final, after, hStart])).mono
      (fun _ _ h => h) fun s st ⟨hL, hst, hPages⟩ => hst ▸ Live.finish_results_oneP (P := Spare a g (spare + 2) pages) hL ⟨final, by
        simp [euler.tryStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩
        fun ha => (hPost1 ha).release_one hLive2.at_
          (hLive2.tempsOwned _ (List.mem_cons_self ..))
          (hFit trial ((step_size _ _ _ (by
            have : grid.size = cells := (hPre ha).1
            omega)).trans (hPre ha).1)) hPages
          (hL.caps.trans hLive2.caps.symm))

theorem tryStep_implements : Implements euler.module 16 tryStepTuple :=
  (tryStep_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

def attemptTuple : UInt64 × Float × Float × Moved (Array Cell) → UInt64 × Float × Array Cell :=
  fun (n, time, dt, grid) => attempt n time dt grid.val

set_option maxHeartbeats 2000000 in
/-- Under `a = false`, the grid has `cells` cells, and the heap has room for two more grids. -/
theorem attempt_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 17 attemptTuple
      (fun x heap store => a = false → x.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 15 euler.attempt.ir "attempt" rfl attemptTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, time, dt, ⟨grid⟩⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl, hGrid⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial
      (Scalar.values n ++ (Scalar.values time ++ (Scalar.values dt ++ [.i64 pGrid])))
      ((n, time, dt, ⟨grid⟩) : UInt64 × Float × Float × Moved (Array Cell)) = [pGrid] := rfl
  rw [hMoves]
  set start := euler.attempt.ir.state
    (Scalar.values n ++ (Scalar.values time ++ (Scalar.values dt ++ [.i64 pGrid])))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.f64 time.toBits) := rfl
  have hGet2 : start.get 2 = some (.f64 dt.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 pGrid) := rfl
  show TripleA _ _ (.ite _ _ _) 7 _ _
  refine Stmt.ite_test (b := validAdvance time dt)
    (by
      simp [Expr.eval, hGet1, hGet2, U64Op.apply, F64Op.apply, word_and, word_beq_one,
        validAdvance, positive, F64Bits.toBits_add, endTime_toBits, Bool.and_assoc])
    (fun hV => ?_) (fun hV => ?_)
  · refine (Live.callOneA (tryStep_implementsA hg spare pages) rfl rfl rfl
      (consumed := [(pGrid, _)]) (rest := [])
      hLive hCap (x := (n, ⟨grid⟩, dt))
      (vals := [.i64 n, .i64 pGrid, .f64 dt.toBits]) (before := start)
      (afterArgs := start)
      (by simp [Expr.evalResults, Expr.eval, hGet0, hGet2, hGet3])
      ⟨_, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, rfl⟩ hPre
      rfl (fun r hr => by simp [Represent.reads] at hr)
      (fun q => ⟨((start.update 6 (.i64 q)).update 5
          (.f64 (tryStepTuple (n, ⟨grid⟩, dt)).2.1.toBits)).update 4
          (.i64 (tryStepTuple (n, ⟨grid⟩, dt)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
    have hy : attemptTuple (n, time, dt, ⟨grid⟩) = tryStepTuple (n, ⟨grid⟩, dt) := by
      simp only [attemptTuple, attempt, hV, tryStepTuple, ite_true]
    rw [hy]
    exact Live.finish_results_oneP (P := Spare a g (spare + 2) pages) hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values] at hst2
      simp [euler.attempt.ir, Expr.evalResults, Expr.eval, ← hst2, hStart, Scalar.values]⟩
      hPost2
  · have hy : attemptTuple (n, time, dt, ⟨grid⟩) = (3, dt, grid) := by
      simp only [attemptTuple, attempt, hV, Bool.false_eq_true, ite_false]
    rw [hy]
    let final := ((start.update 4 (.i64 3)).update 5 (.f64 dt.toBits)).update 6 (.i64 pGrid)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet2, hGet3, final], ?_⟩
    exact Live.finish_results_oneP (P := Spare a g (spare + 2) pages) hLive ⟨final, by
      simp [euler.attempt.ir, Expr.evalResults, Expr.eval, final, hStart, Scalar.values]⟩
      fun ha => (hPre ha).2

theorem attempt_implements : Implements euler.module 17 attemptTuple :=
  (attempt_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

def advanceWithTuple : UInt64 × Float × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, time, dt, grid) => advanceWith n time dt grid.val

set_option maxHeartbeats 4000000 in
/-- Under `a = false`, the grid has `cells` cells, and the heap has room for two more grids. -/
theorem advanceWith_implementsA {aborts : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA aborts euler.module 18 advanceWithTuple
      (fun x heap store => aborts = false → x.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 16 euler.advanceWith.ir "advanceWith" rfl
    advanceWithTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, time, dt, ⟨grid⟩⟩ heap initial _ hHeap hPre
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
  let s3 := s2.update 6 (.i64 pGrid)
  have hS3 : s3.params.length + s3.locals.length = 12 := by simp [s3, s2, hStart]
  have hT : ∀ j, j < 4 → s3.get j = start.get j := fun j hj => by
    simp only [s3, s2]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega),
      State.get_update_ne (by omega)]
  show TripleA _ _ (.seq (.assign 4 (.const 9)) (.seq (.assign 5 (.getF 2))
    (.seq (.assign 6 (.get 3)) (.seq (Stmt.repeatWhile [4, 5, 6] 7 8 (.const 2048)
      ((Expr.get 4).eq (.const 9)) 17 _) _)))) 12 _ _
  refine Stmt.seq_run ⟨start.update 4 (.i64 9), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet2, s2], ?_⟩
  refine Stmt.seq_run ⟨s3, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet3, s2, s3], ?_⟩
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := advanceWith_loop n time dt grid
  let F : UInt64 × Float × Array Cell → UInt64 × Float × Float × Moved (Array Cell) :=
    fun x => (n, time, x.2.1, ⟨x.2.2⟩)
  let Hold : UInt64 × Float × Array Cell → Heap → Store Unit → Prop := fun x heap s =>
    aborts = false → x.2.2.size = cells ∧ heap.Bounded s euler.module g (spare + 2) pages
  have hSmall := hg.cells
  refine Stmt.seq_spec (Live.repeatWhileOneA (attempt_implementsA hg spare pages) rfl rfl rfl
    (by decide) (by decide) (by omega)
    (n := 2048) ⟨s3, by simp [Expr.eval]⟩ cond step F (fun x => (hStepEq x).symm) Hold
    (fun x _ _ _ _ hH _ hP ha => ⟨by
      rw [hStepEq]
      exact (attempt_size n time x.2.1 x.2.2 (by have := (hH ha).1; omega)).trans (hH ha).1,
      hP ha⟩)
    (x0 := ((9 : UInt64), dt, grid)) (p0 := pGrid) hLive
    (by
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
      · simp [s3, s2, hStart]
      · simp [s3, s2, hStart]
      · simp [s3, s2, hStart])
    hPre hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have h4 : st.get 4 = some (.i64 a) := by
      simp [State.Holds, Scalar.values] at hHolds
      exact hHolds.1
    exact ⟨st, by simp [Expr.eval, h4, hCondEq]⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hHoldX hFrame
    have hG : ∀ j, j < 4 → st.get j = start.get j := fun j hj =>
      (hFrame.get j (by omega) (by simp; omega)).trans (hT j hj)
    have hH : st.get 4 = some (.i64 a) ∧ st.get 5 = some (.f64 b.toBits) ∧
        st.get 6 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_cons_self ..)
    refine ⟨[.i64 n, .f64 time.toBits, .f64 b.toBits, .i64 p], st, ?_,
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOld⟩, hHoldX, rfl,
      fun q hq => by simp [Represent.reads] at hq⟩
    simp [Expr.evalResults, Expr.eval, hG 0 (by decide), hG 1 (by decide), hH.2.1, hH.2.2,
      hGet0, hGet1]
  · apply TripleA.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4, hHold4⟩
    generalize hR : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step = R
      at hL4 hHolds4 hHold4
    obtain ⟨a, b, c⟩ := R
    have hy : advanceWithTuple (n, time, dt, ⟨grid⟩) = (if a == 0 then ((0 : UInt64), time + b, c)
        else (if a == 9 then 4 else a, time, c)) := by
      show advanceWith n time dt grid = _
      rw [hDef, hR]
    rw [hy]
    have hLen4 : st4.params.length + st4.locals.length = 12 := by
      rw [hFrame4.params, hFrame4.locals]; exact hS3
    have hG : ∀ j, j < 4 → st4.get j = start.get j := fun j hj =>
      (hFrame4.get j (by omega) (by simp; omega)).trans (hT j hj)
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
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL4 ⟨final, by
        simp [euler.advanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩
        fun ha => (hHold4 ha).2
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 9 (.i64 (if a == 9 then 4 else a))).update 10
        (.f64 time.toBits)).update 11 (.i64 p4)
      refine Stmt.seq_run ⟨st4.update 9 (.i64 (if a == 9 then 4 else a)), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1], ?_⟩
      refine Stmt.seq_run ⟨(st4.update 9 (.i64 (if a == 9 then 4 else a))).update 10
          (.f64 time.toBits), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 1 (by decide), hGet1], ?_⟩
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL4 ⟨final, by
        simp [euler.advanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩
        fun ha => (hHold4 ha).2

theorem advanceWith_implements : Implements euler.module 18 advanceWithTuple :=
  (advanceWith_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

def advanceStepTuple : UInt64 × UInt64 × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, status, time, grid) => advanceStep n status time grid.val

set_option maxHeartbeats 4000000 in
/-- Under `a = false`, the grid has `cells` cells, and the heap has room for two more grids. -/
theorem advanceStep_implementsA {aborts : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA aborts euler.module 19 advanceStepTuple
      (fun x heap store => aborts = false → x.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 17 euler.advanceStep.ir "advanceStep" rfl
    advanceStepTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, status, time, ⟨grid⟩⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl, hGrid⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial
      (Scalar.values n ++ (Scalar.values status ++ (Scalar.values time ++ [.i64 pGrid])))
      ((n, status, time, ⟨grid⟩) : UInt64 × UInt64 × Float × Moved (Array Cell)) = [pGrid] :=
    rfl
  rw [hMoves]
  set start := euler.advanceStep.ir.state
    (Scalar.values n ++ (Scalar.values status ++ (Scalar.values time ++ [.i64 pGrid])))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet2 : start.get 2 = some (.f64 time.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 pGrid) := rfl
  let stats := scan grid
  let after := (start.update 5 (.f64 stats.2.toBits)).update 4 (.i64 stats.1)
  show TripleA _ _ (.seq (.call 15 [⟨.u64, .get 3⟩] [4, 5]) _) 11 _ _
  refine Live.callScalar_seqA scan_implementsA rfl rfl rfl hLive hCap (x := grid)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet3])
    ⟨pGrid, rfl, (hLive.tempsOwned (pGrid, flatWords grid) (by simp)).borrowed⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, stats]) ?_
  rintro heap1 s1 hLive1 ⟨rfl, rfl⟩
  refine Stmt.ite_test (b := stats.1 == 0) (by simp [Expr.eval, after, hStart])
    (fun hS => ?_) (fun hS => ?_)
  · let a := 0.4 * spacing n / stats.2
    let b := endTime - time
    have hy : advanceStepTuple (n, status, time, ⟨grid⟩) =
        advanceWithTuple (n, time, proposal n time stats.2, ⟨grid⟩) := by
      simp only [advanceStepTuple, advanceStep, advanceWithTuple, hS, ite_true, stats]
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
    refine (Live.callOneA (advanceWith_implementsA hg spare pages) rfl rfl rfl
      (consumed := [(pGrid, _)])
      (rest := []) hLive1 hCap (x := (n, time, proposal n time stats.2, ⟨grid⟩))
      (vals := [.i64 n, .f64 time.toBits, .f64 (proposal n time stats.2).toBits, .i64 pGrid])
      (before := s10) (afterArgs := s10)
      (by
        by_cases hc : a.toBits ≤ b.toBits
        · simp [Expr.evalResults, Expr.eval, s10, s9, after, hStart, hGet0, hGet2, hGet3,
            proposal, hc, a, b]
        · simp [Expr.evalResults, Expr.eval, s10, s9, after, hStart, hGet0, hGet2, hGet3,
            proposal, hc, a, b])
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
        hLive1.tempsOwned (pGrid, flatWords grid) (by simp)⟩ hPre
      rfl (fun r hr => by simp [Represent.reads] at hr)
      (fun q => ⟨((s10.update 8 (.i64 q)).update 7
          (.f64 (advanceWithTuple (n, time, proposal n time stats.2, ⟨grid⟩)).2.1.toBits)).update 6
          (.i64 (advanceWithTuple (n, time, proposal n time stats.2, ⟨grid⟩)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, s10, s9, after, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, s10, s9, after, Scalar.values] at hst2
      simp [euler.advanceStep.ir, Expr.evalResults, Expr.eval, ← hst2, hStart, Scalar.values]⟩
      hPost2
  · have hy : advanceStepTuple (n, status, time, ⟨grid⟩) = (2, time, grid) := by
      simp only [advanceStepTuple, advanceStep, hS, Bool.false_eq_true, ite_false, stats]
    rw [hy]
    let final := ((after.update 6 (.i64 2)).update 7 (.f64 time.toBits)).update 8 (.i64 pGrid)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, after, hGet2, hGet3, final], ?_⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive1 ⟨final, by
      simp [euler.advanceStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
        Scalar.values]⟩ fun ha => (hPre ha).2

theorem advanceStep_implements : Implements euler.module 19 advanceStepTuple :=
  (advanceStep_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

set_option maxHeartbeats 4000000 in
/-- Under `a = false`, `n * n` is `cells`, and the heap has room for three more grids. -/
theorem runFrom_implementsA {aborts : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA aborts euler.module 20 runFrom
      (fun n heap store => aborts = false → (n * n).toNat = cells ∧
        heap.Bounded store euler.module g (spare + 3) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_heapA euler.funcs 18 euler.runFrom.ir "runFrom" rfl runFrom _ _
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap hPre rfl hCap
  set start := euler.runFrom.ir.state (Scalar.values n) with hStartDef
  have hStart : start.params.length + start.locals.length = 9 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  let s2 := (start.update 1 (.i64 0)).update 2 (.f64 0)
  show TripleA _ _ (.seq (.assign 1 (.const 0)) (.seq (.assign 2 (.constF 0))
    (.seq (.call 10 [⟨.u64, .get 0⟩] [3]) (.seq (Stmt.repeatWhile [1, 2, 3] 4 5
      (.const 4294967296) _ 19 _) _)))) 9 _ _
  refine Stmt.seq_run ⟨start.update 1 (.i64 0), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
  refine Live.callOne_seqA (initialCells_implementsA hg (spare + 2) pages) rfl rfl rfl
    (consumed := []) (Live.start hHeap)
    hCap (x := n) (vals := [.i64 n]) (before := s2) (afterArgs := s2)
    (by simp [Expr.evalResults, Expr.eval, s2, hGet0]) rfl hPre rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨s2.update 3 (.i64 q), by simp [State.setAll, State.set?_eq_update, s2, hStart]⟩) ?_
  intro heap1 p1 s3 st3 hLive1 hst3 hPost1
  have hst : st3 = s2.update 3 (.i64 p1) := by
    simp [State.setAll, State.set?_eq_update, s2, hStart] at hst3
    exact hst3.symm
  subst hst
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := runFrom_loop n
  let F : UInt64 × Float × Array Cell → UInt64 × UInt64 × Float × Moved (Array Cell) :=
    fun x => (n, x.1, x.2.1, ⟨x.2.2⟩)
  let Hold : UInt64 × Float × Array Cell → Heap → Store Unit → Prop := fun x heap s =>
    aborts = false → x.2.2.size = cells ∧ heap.Bounded s euler.module g (spare + 2) pages
  have hSmall := hg.cells
  have hS3 : (s2.update 3 (.i64 p1)).params.length + (s2.update 3 (.i64 p1)).locals.length = 9 :=
    by simp [s2, hStart]
  refine Stmt.seq_spec (Live.repeatWhileOneA (advanceStep_implementsA hg spare pages) rfl rfl rfl
    (by decide) (by decide) (by omega) (n := 4294967296) ⟨s2.update 3 (.i64 p1), by simp [Expr.eval]⟩
    cond step F (fun x => (hStepEq x).symm) Hold
    (fun x _ _ _ _ hH _ hP ha => ⟨by
      rw [hStepEq]
      exact (advanceStep_size (by have := (hH ha).1; omega)).trans (hH ha).1, hP ha⟩)
    (x0 := ((0 : UInt64), (0 : Float), initialCells n)) (p0 := p1) hLive1
    (by simp [State.Holds, s2, hStart, Scalar.values, zero_toBits])
    (fun ha => ⟨(initialCells_size n).trans (hPre ha).1, hPost1 ha⟩) hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have hH : st.get 1 = some (.i64 a) ∧ st.get 2 = some (.f64 b.toBits) := by
      simp [State.Holds, Scalar.values] at hHolds
      exact ⟨hHolds.1, hHolds.2.1⟩
    exact ⟨st, by
      simp [Expr.eval, hH.1, hH.2, hCondEq, word_and_not, word_beq_one, endTime_toBits,
        U64Op.apply]
      rw [Bool.eq_iff_iff]
      simp⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hHoldX hFrame
    have hG0 : st.get 0 = some (.i64 n) :=
      (hFrame.get 0 (by omega) (by simp)).trans (by simp [s2, hGet0])
    have hH : st.get 1 = some (.i64 a) ∧ st.get 2 = some (.f64 b.toBits) ∧
        st.get 3 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_singleton_self _)
    have hF : F (a, b, c) = (n, a, b, ⟨c⟩) := rfl
    rw [hF]
    refine ⟨[.i64 n, .i64 a, .f64 b.toBits, .i64 p], st, ?_,
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOld⟩, hHoldX, rfl,
      fun q hq => by simp [Represent.reads] at hq⟩
    simp [Expr.evalResults, Expr.eval, hG0, hH.1, hH.2.1, hH.2.2]
  · apply TripleA.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4, hHold4⟩
    generalize hR : LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n)
      cond step = R at hL4 hHolds4 hHold4
    obtain ⟨a, b, c⟩ := R
    have hy : runFrom n = (if a == 0 && b.toBits != endTime.toBits then (5, b, c) else (a, b, c)) :=
      by rw [hDef, hR]
    rw [hy]
    have hLen4 : st4.params.length + st4.locals.length = 9 := by
      rw [hFrame4.params, hFrame4.locals]; exact hS3
    have hH : st4.get 1 = some (.i64 a) ∧ st4.get 2 = some (.f64 b.toBits) ∧
        st4.get 3 = some (.i64 p4) := by
      simpa [State.Holds, Scalar.values] using hHolds4
    refine Stmt.ite_test (b := a == 0 && b.toBits != endTime.toBits)
      (by
        simp [Expr.eval, hH.1, hH.2.1, word_and_not, word_beq_one, endTime_toBits, U64Op.apply]
        rw [Bool.eq_iff_iff]
        simp)
      (fun hA => ?_) (fun hA => ?_)
    · simp only [hA, ite_true]
      let final := ((st4.update 6 (.i64 5)).update 7 (.f64 b.toBits)).update 8 (.i64 p4)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.1, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) (y := ((5 : UInt64), b, c)) hL4 ⟨final, by
        simp [euler.runFrom.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩
        fun ha => (hHold4 ha).2
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 6 (.i64 a)).update 7 (.f64 b.toBits)).update 8 (.i64 p4)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1, hH.2.1, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL4 ⟨final, by
        simp [euler.runFrom.ir, Expr.evalResults, Expr.eval, final, hLen4, Scalar.values]⟩
        fun ha => (hHold4 ha).2

theorem runFrom_implements : Implements euler.module 20 runFrom :=
  (runFrom_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

set_option maxHeartbeats 2000000 in
/-- Under `a = false`, `n * n` is `cells` when `n` is in range, and the heap has room for three
more grids. -/
theorem run_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 21 Examples.Euler.run
      (fun n heap store => a = false → ((2 ≤ n && n ≤ 800) = true → (n * n).toNat = cells) ∧
        heap.Bounded store euler.module g (spare + 3) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_heapA euler.funcs 19 euler.run.ir "run" rfl Examples.Euler.run
    _ _ (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap hPre rfl hCap
  set start := euler.run.ir.state (Scalar.values n) with hStartDef
  have hStart : start.params.length + start.locals.length = 4 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  show TripleA _ _ (.ite _ (.call 20 [⟨.u64, .get 0⟩] [1, 2, 3]) (.seq (.assign 1 (.const 1))
    (.seq (.assign 2 (.constF 0)) (Stmt.arrayLiteral 3 [])))) 4 _ _
  refine Stmt.ite_test (b := 2 ≤ n && n ≤ 800)
    (by simp [Expr.eval, hGet0, word_and, word_beq_one, U64Op.apply]) (fun hN => ?_)
    (fun hN => ?_)
  · have hy : Examples.Euler.run n = runFrom n := by
      simp [Examples.Euler.run, hN]
    rw [hy]
    refine (Live.callOneA (runFrom_implementsA hg spare pages) rfl rfl rfl (consumed := [])
      (Live.start hHeap) hCap
      (x := n) (vals := [.i64 n]) (before := start) (afterArgs := start)
      (by simp [Expr.evalResults, Expr.eval, hGet0]) rfl
      (fun ha => ⟨(hPre ha).1 hN, (hPre ha).2⟩) rfl (fun _ _ _ h => nomatch h)
      (fun q => ⟨((start.update 3 (.i64 q)).update 2 (.f64 (runFrom n).2.1.toBits)).update 1
          (.i64 (runFrom n).1), by
        simp [State.setAll, State.set?_eq_update, hStart, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
    exact Live.finish_results_oneP (P := Spare a g (spare + 2) pages) hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values] at hst2
      simp [euler.run.ir, Expr.evalResults, Expr.eval, ← hst2, hStart, Scalar.values]⟩ hPost2
  · have hy : Examples.Euler.run n = (1, 0, #[]) := by
      simp [Examples.Euler.run, hN]
    rw [hy]
    let s2 := (start.update 1 (.i64 1)).update 2 (.f64 0)
    refine Stmt.seq_run ⟨start.update 1 (.i64 1), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
    refine Stmt.seq_run ⟨s2, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
    have hNeed : UInt64.ofNat (8 * (([] : List (Expr .u64)).length + 1)) ≤ g := by
      have := hg.eight
      rw [UInt64.le_iff_toNat_le]
      simpa using this
    refine (Stmt.arrayLiteral_specA (values := []) (words := []) rfl rfl rfl (by decide)
      (by simp [s2, hStart]) hHeap hCap
      (fun ha => (hPre ha).2.room hHeap (by omega) hNeed hg.eight hCap) (by decide) .nil).mono
      (fun _ _ h => h) ?_
    rintro s st ⟨p, hFrame, hP, hNew, hPages⟩
    have hLen : st.params.length + st.locals.length = 4 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, hStart]
    have hG : ∀ j, j < 3 → st.get j = s2.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    exact Live.finish_results_oneP (P := Spare a g (spare + 2) pages) (y := ((1 : UInt64), (0 : Float), (#[] : Array Cell)))
      (Live.push (Live.start hHeap) hNew) ⟨st, by
        simp [euler.run.ir, Expr.evalResults, Expr.eval, hP, hG 1 (by decide), hG 2 (by decide),
          s2, hStart, Scalar.values, zero_toBits]⟩
      fun ha => (hPre ha).2.allocate hHeap hNeed hg.eight hCap hPages hNew.caps

theorem run_implements : Implements euler.module 21 Examples.Euler.run :=
  (run_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

/-- The grid of a run has at most `cells` cells when `n * n` is `cells` for `n` in range. -/
theorem run_grid_size (n : UInt64) {cells : Nat}
    (h : (2 ≤ n && n ≤ 800) = true → (n * n).toNat = cells) :
    (Examples.Euler.run n).2.2.size ≤ cells := by
  unfold Examples.Euler.run
  split
  · rename_i hn
    rw [runFrom_size, h hn]
  · simp

set_option maxHeartbeats 2000000 in
/-- Under `a = false`, `n * n` is `cells` when `n` is in range, `cells` is positive, and the heap
has room for three more grids. -/
theorem solve_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 23 solve
      (fun n heap store => a = false → ((2 ≤ n && n ≤ 800) = true → (n * n).toNat = cells) ∧
        1 ≤ cells ∧ heap.Bounded store euler.module g (spare + 3) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final euler.module g (spare + 1) pages) := by
  refine Func.implements_heapA euler.funcs 21 euler.solve.ir "solve" rfl solve _ _
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap hPre rfl hCap
  set start := euler.solve.ir.state (Scalar.values n) with hStartDef
  have hStart : start.params.length + start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      Examples.Euler.run n = (status, time, grid) :=
    ⟨_, _, _, rfl⟩
  have hGridSize : a = false → grid.size ≤ cells := fun ha => by
    have := run_grid_size n (hPre ha).1
    rw [hRun] at this
    exact this
  have hy : solve n = packTuple (n, status, time, grid) := by simp [solve, hRun, packTuple]
  rw [hy]
  let s1 := ((start.update 3 (.i64 0)).update 2 (.f64 time.toBits)).update 1 (.i64 status)
  show TripleA _ _ (.seq (.call 21 [⟨.u64, .get 0⟩] [1, 2, 3]) (.seq (.call 22 _ [4])
    (.seq (.assign 5 (.get 4)) (.call 1 [⟨.u64, .get 3⟩] [])))) 6 _ _
  refine Live.callOne_seqA (run_implementsA hg spare pages) rfl rfl rfl (consumed := [])
    (Live.start hHeap) hCap
    (x := n) (vals := [.i64 n]) (before := start) (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0]) rfl
    (fun ha => ⟨(hPre ha).1, (hPre ha).2.2⟩) rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨((start.update 3 (.i64 q)).update 2 (.f64 time.toBits)).update 1 (.i64 status), by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values, hRun]⟩) ?_
  intro heap1 pg s2 st2 hLive1 hst2 hPost1
  have hst : st2 = ((start.update 3 (.i64 pg)).update 2 (.f64 time.toBits)).update 1
      (.i64 status) := by
    simp [State.setAll, State.set?_eq_update, hStart, Scalar.values, hRun] at hst2
    exact hst2.symm
  subst hst
  rw [hRun] at hLive1
  let s3 := ((start.update 3 (.i64 pg)).update 2 (.f64 time.toBits)).update 1 (.i64 status)
  refine Live.callOne_seqA (pack_implementsA (g := g) (spare + 1) pages) rfl rfl rfl
    (consumed := []) hLive1 hCap
    (x := (n, status, time, grid)) (vals := [.i64 n, .i64 status, .f64 time.toBits, .i64 pg])
    (before := s3) (afterArgs := s3)
    (by simp [Expr.evalResults, Expr.eval, hGet0, s3, hStart])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pg, rfl,
      (hLive1.tempsOwned (pg, flatWords grid) (by simp)).borrowed⟩
    (fun ha => ⟨show 8 * (2 * grid.size + 5) ≤ g.toNat by
      have := hg.bytes
      have := hGridSize ha
      have := (hPre ha).2.1
      omega, hg.eight, hPost1 ha⟩) rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨s3.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart, s3]⟩) ?_
  intro heap2 pk s4 st4 hLive2 hst4 hPost2
  have hst : st4 = s3.update 4 (.i64 pk) := by
    simp [State.setAll, State.set?_eq_update, hStart, s3] at hst4
    exact hst4.symm
  subst hst
  let final := (s3.update 4 (.i64 pk)).update 5 (.i64 pk)
  refine Stmt.seq_run ⟨final, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s3, final], ?_⟩
  exact Live.releaseSecond_last_pages hLive2 rfl rfl (by simp [final, s3, hStart])
    fun s hL hPages => Live.finish_results_oneP (P := Spare a g (spare + 1) pages) hL ⟨final, by
      simp [euler.solve.ir, Expr.evalResults, Expr.eval, final, s3, hStart]⟩
      fun ha => (hPost2 ha).release hLive2.at_ (hLive2.tempsOwned (pg, flatWords grid) (by simp))
        hPages (hL.caps.trans hLive2.caps.symm)

theorem solve_implements : Implements euler.module 23 solve :=
  (solve_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

end Examples.Euler
