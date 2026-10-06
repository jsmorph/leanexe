import Examples.Euler.ReconstructedSteps
import Examples.Euler.ReconstructedSpec

/-! The compiled functions of the reconstructed Euler solver that pass grids by moves compute
their Lean definitions. -/

namespace Examples.Euler

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime LeanExe.ProofKit Examples.Euler

def reconstructedFinishTuple : UInt64 × UInt64 × Float × Moved (Array Cell) → Array Cell :=
  fun (n, trials, ratio, middle) => reconstructedFinish n trials ratio middle.val

/-- Under `aborts = false`, the middle grid has `cells` cells, and the heap has room for one more grid. -/
theorem reconstructedFinish_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 45 reconstructedFinishTuple
      (fun x heap store => aborts = false → x.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 1) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 1) pages) := by
  refine Func.implements_movesA euler.funcs 43 euler.reconstructedFinish.ir "reconstructedFinish"
    rfl reconstructedFinishTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, trials, ratio, ⟨middle⟩⟩ heap initial _ hHeap hPre
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
  show TripleA _ _ (.seq (.call 12 [⟨.u64, .get 3⟩] [5]) _) 6 _ _
  refine Live.callScalar_seqA accepted_implementsA rfl rfl rfl hLive hCap (x := middle)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet3])
    ⟨p, rfl, hMid.borrowed⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  rintro heap1 s1 hLive1 ⟨rfl, rfl⟩
  refine Stmt.ite_test (b := accepted middle)
    (by cases h : accepted middle <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · refine Live.callOne_seqA (reconstructedSweep_implementsA hg spare pages) rfl rfl rfl
      (consumed := []) hLive1 hCap
      (x := (n, true, trials, ratio, middle))
      (vals := [.i64 n, .i64 1, .i64 trials, .f64 ratio.toBits, .i64 p])
      (before := after) (afterArgs := after)
      (by simp [Expr.evalResults, Expr.eval, after, hGet0, hGet1, hGet2, hGet3])
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl,
        (hLive1.tempsOwned (p, flatWords middle) (by simp)).borrowed⟩ hPre rfl
      (fun _ _ _ h => nomatch h)
      (fun q => ⟨after.update 4 (.i64 q), by
        simp [State.setAll, State.set?_eq_update, after, hStart]⟩) ?_
    intro heap2 ptr s2 st2 hLive2 hst2 hPost2
    have hst : st2 = after.update 4 (.i64 ptr) := by
      simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
      exact hst2.symm
    subst hst
    have hy : reconstructedFinishTuple (n, trials, ratio, ⟨middle⟩) =
        reconstructedSweepTuple (n, true, trials, ratio, middle) := by
      simp [reconstructedFinishTuple, reconstructedFinish, hA, reconstructedSweepTuple]
    rw [hy]
    exact Live.releaseSecond_last_pages hLive2 rfl rfl (by simp [after, hGet3])
      fun s hL hPages => Live.finish_results_oneP (P := Spare aborts g (spare + 1) pages) hL
        ⟨after.update 4 (.i64 ptr), by
          simp [euler.reconstructedFinish.ir, Expr.evalResults, Expr.eval, after, hStart]⟩
        fun ha => (hPost2 ha).release_one hLive2.at_
          (hLive2.tempsOwned (p, flatWords middle) (by simp))
          (by rw [flatWords_size cell_length, (hPre ha).1, hg.bytes]) hPages
          (hL.caps.trans hLive2.caps.symm)
  · have hy : reconstructedFinishTuple (n, trials, ratio, ⟨middle⟩) = middle := by
      simp [reconstructedFinishTuple, reconstructedFinish, hA]
    rw [hy]
    refine Stmt.run_triple ⟨after.update 4 (.i64 p), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet3], ?_⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 1) pages) hLive1
      ⟨after.update 4 (.i64 p), by
        simp [euler.reconstructedFinish.ir, Expr.evalResults, Expr.eval, after, hStart]⟩
      fun ha => (hPre ha).2

theorem reconstructedFinish_implements : Implements euler.module 45 reconstructedFinishTuple :=
  (reconstructedFinish_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

def reconstructedStepGridTuple : UInt64 × UInt64 × Float × Array Cell → Array Cell :=
  fun (n, trials, ratio, grid) => reconstructedStepGrid n trials ratio grid

/-- Under `aborts = false`, the grid has `cells` cells, and the heap has room for two more grids. -/
theorem reconstructedStepGrid_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 46 reconstructedStepGridTuple
      (fun x heap store => aborts = false → x.2.2.2.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 1) pages) := by
  refine Func.implements_heapA euler.funcs 44 euler.reconstructedStepGrid.ir
    "reconstructedStepGrid" rfl reconstructedStepGridTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, trials, ratio, grid⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ hCap
  change heap.Borrowed initial p (flatWords grid) at hGrid
  set start := euler.reconstructedStepGrid.ir.state (Scalar.values n ++ (Scalar.values trials ++
    (Scalar.values ratio ++ [.i64 p]))) with hStartDef
  have hStart : start.params.length + start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 ratio.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 p) := rfl
  show TripleA _ _ (.seq (.call 44 _ [4]) (.call 45 _ [5])) 6 _ _
  refine Live.callOne_seqA (reconstructedSweep_implementsA hg (spare + 1) pages) rfl rfl rfl
    (consumed := [])
    (Live.start hHeap) hCap (x := (n, false, trials, ratio, grid))
    (vals := [.i64 n, .i64 0, .i64 trials, .f64 ratio.toBits, .i64 p]) (before := start)
    (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2, hGet3])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hGrid⟩ hPre rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1 hPost1
  have hst : st1 = start.update 4 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let after := start.update 4 (.i64 ptr)
  refine (Live.callOneA (reconstructedFinish_implementsA hg spare pages) rfl rfl rfl
    (consumed := [(ptr, _)]) (rest := []) hLive1 hCap
    (x := (n, trials, ratio, ⟨reconstructedSweep n false trials ratio grid⟩))
    (vals := [.i64 n, .i64 trials, .f64 ratio.toBits, .i64 ptr]) (before := after)
    (afterArgs := after)
    (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1, hGet2])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl,
      hLive1.tempsOwned _ (List.mem_singleton_self _)⟩
    (fun ha => ⟨by
      have := hg.cells
      have : grid.size = cells := (hPre ha).1
      rw [reconstructedSweep_size _ _ _ _ _ (by omega)]; exact (hPre ha).1, hPost1 ha⟩)
    rfl (fun _ h => by simp [Represent.reads] at h)
    (fun q => ⟨after.update 5 (.i64 q), by simp [State.setAll, State.set?_eq_update, after,
      hStart]⟩)).mono (fun _ _ h => h) ?_
  rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
  have hst : st = after.update 5 (.i64 ptr2) := by
    simp [State.setAll, State.set?_eq_update, after, hStart] at hst2
    exact hst2.symm
  subst hst
  exact Live.finish_results_oneP (P := Spare aborts g (spare + 1) pages)
    (y := reconstructedStepGridTuple (n, trials, ratio, grid)) hLive2
    ⟨after.update 5 (.i64 ptr2), by simp [euler.reconstructedStepGrid.ir, Expr.evalResults,
      Expr.eval, after, hStart]⟩ hPost2

theorem reconstructedStepGrid_implements : Implements euler.module 46 reconstructedStepGridTuple :=
  (reconstructedStepGrid_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

def reconstructedTryTuple : UInt64 × UInt64 × Moved (Array Cell) × Float × Float →
    UInt64 × Float × Array Cell :=
  fun (n, trials, grid, ratio, dt) => reconstructedTry n trials grid.val ratio dt

set_option maxHeartbeats 2000000 in
/-- Under `aborts = false`, the grid has `cells` cells, and the heap has room for two more
grids. -/
theorem reconstructedTry_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 50 reconstructedTryTuple
      (fun x heap store => aborts = false → x.2.2.1.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 48 euler.reconstructedTry.ir "reconstructedTry" rfl
    reconstructedTryTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨n, trials, ⟨grid⟩, ratio, dt⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, rfl⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values trials ++
      ([.i64 pGrid] ++ Scalar.values (ratio, dt))))
      ((n, trials, ⟨grid⟩, ratio, dt) : UInt64 × UInt64 × Moved (Array Cell) × Float × Float) =
        [pGrid] := rfl
  rw [hMoves]
  set start := euler.reconstructedTry.ir.state (Scalar.values n ++ (Scalar.values trials ++
      ([.i64 pGrid] ++ Scalar.values (ratio, dt)))) with hStartDef
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.i64 pGrid) := rfl
  have hGet3 : start.get 3 = some (.f64 ratio.toBits) := rfl
  have hGet4 : start.get 4 = some (.f64 dt.toBits) := rfl
  have hSmall := hg.cells
  show TripleA _ _ (.seq (.call 46 _ [5]) (.seq (.call 12 _ [9]) _)) 10 _ _
  refine Live.callOne_seqA (reconstructedStepGrid_implementsA hg spare pages) rfl rfl rfl
    (consumed := []) hLive hCap
    (x := (n, trials, ratio, grid))
    (vals := [.i64 n, .i64 trials, .f64 ratio.toBits, .i64 pGrid]) (before := start)
    (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1, hGet2, hGet3])
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
      (hLive.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩ hPre rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨start.update 5 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart]⟩) ?_
  intro heap1 ptr s1 st1 hLive1 hst1 hPost1
  have hst : st1 = start.update 5 (.i64 ptr) := by
    simp [State.setAll, State.set?_eq_update, hStart] at hst1
    exact hst1.symm
  subst hst
  let trial := reconstructedStepGrid n trials ratio grid
  let after := (start.update 5 (.i64 ptr)).update 9 (.i64 (if accepted trial then 1 else 0))
  refine Live.callScalar_seqA accepted_implementsA rfl rfl rfl hLive1 hCap (x := trial)
    (before := start.update 5 (.i64 ptr)) (afterArgs := start.update 5 (.i64 ptr))
    (after := after) (by simp [Expr.evalResults, Expr.eval, hStart])
    ⟨ptr, rfl, (hLive1.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat]) ?_
  rintro heap2 s2 hLive2 ⟨rfl, rfl⟩
  have hFit : ∀ (c : Array Cell), c.size = cells → g.toNat ≤ 8 * ((flatWords c).size + 1) :=
    fun c hc => by rw [flatWords_size cell_length, hc, hg.bytes]
  refine Stmt.ite_test (b := accepted trial)
    (by cases h : accepted trial <;> simp [Expr.eval, after, hStart, h])
    (fun hA => ?_) (fun hA => ?_)
  · have hy : reconstructedTryTuple (n, trials, ⟨grid⟩, ratio, dt) =
        (0, dt, reconstructedStepGridTuple (n, trials, ratio, grid)) := by
      simp [reconstructedTryTuple, reconstructedTry, reconstructedStepGridTuple, hA, trial]
    rw [hy]
    let final := ((after.update 6 (.i64 0)).update 7 (.f64 dt.toBits)).update 8 (.i64 ptr)
    refine Stmt.seq_run ⟨after.update 6 (.i64 0), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 6 (.i64 0)).update 7 (.f64 dt.toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet4], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final], ?_⟩
    exact Live.releaseSecond_last_pages hLive2 rfl rfl (by simp [final, after, hGet2])
      fun s hL hPages => Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL
        ⟨final, by
          simp [euler.reconstructedTry.ir, Expr.evalResults, Expr.eval, final, after, hStart,
            Scalar.values]⟩
        fun ha => (hPost1 ha).release_one hLive2.at_
          (hLive2.tempsOwned (pGrid, flatWords grid) (by simp)) (hFit grid (hPre ha).1) hPages
          (hL.caps.trans hLive2.caps.symm)
  · have hy : reconstructedTryTuple (n, trials, ⟨grid⟩, ratio, dt) = (9, 0.5 * dt, grid) := by
      simp [reconstructedTryTuple, reconstructedTry, hA, trial]
    rw [hy]
    let final := ((after.update 6 (.i64 9)).update 7 (.f64 (0.5 * dt).toBits)).update 8
      (.i64 pGrid)
    refine Stmt.seq_run ⟨after.update 6 (.i64 9), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart], ?_⟩
    refine Stmt.seq_run ⟨(after.update 6 (.i64 9)).update 7 (.f64 (0.5 * dt).toBits), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet4, F64Op.apply,
        F64Bits.toBits_mul, half_toBits], ?_⟩
    refine Stmt.seq_run ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, final, hGet2], ?_⟩
    exact ((hLive2.releaseFirst_pages rfl rfl (by simp [final, after, hStart])).mono
      (fun _ _ h => h) fun s st ⟨hL, hst, hPages⟩ => hst ▸
        Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL ⟨final, by
          simp [euler.reconstructedTry.ir, Expr.evalResults, Expr.eval, final, after, hStart,
            Scalar.values]⟩
        fun ha => (hPost1 ha).release_one hLive2.at_
          (hLive2.tempsOwned _ (List.mem_cons_self ..))
          (hFit trial ((reconstructedStepGrid_size _ _ _ _ (by
            have : grid.size = cells := (hPre ha).1
            omega)).trans (hPre ha).1)) hPages
          (hL.caps.trans hLive2.caps.symm))

theorem reconstructedTry_implements : Implements euler.module 50 reconstructedTryTuple :=
  (reconstructedTry_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

def reconstructedAttemptTuple : UInt64 × UInt64 × Float × Float × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, trials, time, alpha, dt, grid) => reconstructedAttempt n trials time alpha dt grid.val

set_option maxHeartbeats 2000000 in
/-- Under `aborts = false`, the grid has `cells` cells, and the heap has room for two more
grids. -/
theorem reconstructedAttempt_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 51 reconstructedAttemptTuple
      (fun x heap store => aborts = false → x.2.2.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 49 euler.reconstructedAttempt.ir
    "reconstructedAttempt" rfl reconstructedAttemptTuple _ _
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl,
        rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, trials, time, alpha, dt, ⟨grid⟩⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, pGrid, rfl,
      hGrid⟩ - hCap
  change heap.Owned initial pGrid (flatWords grid) at hGrid
  have hLive := Live.start_moved hHeap (temps := [(pGrid, flatWords grid)])
    (by simpa using hGrid) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values alpha ++ (Scalar.values dt ++ [.i64 pGrid])))))
      ((n, trials, time, alpha, dt, ⟨grid⟩) :
        UInt64 × UInt64 × Float × Float × Float × Moved (Array Cell)) = [pGrid] := rfl
  rw [hMoves]
  set start := euler.reconstructedAttempt.ir.state (Scalar.values n ++ (Scalar.values trials ++
      (Scalar.values time ++ (Scalar.values alpha ++ (Scalar.values dt ++ [.i64 pGrid])))))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  have hGet2 : start.get 2 = some (.f64 time.toBits) := rfl
  have hGet3 : start.get 3 = some (.f64 alpha.toBits) := rfl
  have hGet4 : start.get 4 = some (.f64 dt.toBits) := rfl
  have hGet5 : start.get 5 = some (.i64 pGrid) := rfl
  let ratio := gridRatio n dt alpha
  let after := (start.update 7 (.f64 ratio.value.toBits)).update 6 (.i64 ratio.status)
  show TripleA _ _ (.seq (.call 49 _ [6, 7]) _) 11 _ _
  refine Stmt.seq_callPure gridRatio_implements rfl rfl rfl (x := (n, dt, alpha)) ⟨start,
    by simp [Expr.evalResults, Expr.eval, hGet0, hGet3, hGet4, Scalar.values], after,
    by simp [State.setAll, State.set?_eq_update, hStart, after, gridRatioTuple, ratio,
      Scalar.values, Flat.flat], ?_⟩
  refine Stmt.ite_test (b := validAdvance time dt)
    (by
      simp [Expr.eval, after, hStart, hGet2, hGet4, U64Op.apply, F64Op.apply, word_and,
        word_beq_one, validAdvance, positive, F64Bits.toBits_add, endTime_toBits,
        Bool.and_assoc])
    (fun hV => ?_) (fun hV => ?_)
  · refine Stmt.ite_test (b := ratio.status == 0) (by simp [Expr.eval, after, hStart])
      (fun hR => ?_) (fun hR => ?_)
    · refine (Live.callOneA (reconstructedTry_implementsA hg spare pages) rfl rfl rfl
        (consumed := [(pGrid, _)]) (rest := []) hLive hCap (x := (n, trials, ⟨grid⟩, ratio.value, dt))
        (vals := [.i64 n, .i64 trials, .i64 pGrid, .f64 ratio.value.toBits, .f64 dt.toBits])
        (before := after) (afterArgs := after)
        (by simp [Expr.evalResults, Expr.eval, after, hStart, hGet0, hGet1, hGet4, hGet5])
        ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨pGrid, rfl, hGrid⟩, rfl⟩ hPre
        rfl (fun r hr => by simp [Represent.reads] at hr)
        (fun q => ⟨((after.update 10 (.i64 q)).update 9 (.f64 (reconstructedTryTuple
            (n, trials, ⟨grid⟩, ratio.value, dt)).2.1.toBits)).update 8
            (.i64 (reconstructedTryTuple (n, trials, ⟨grid⟩, ratio.value, dt)).1), by
          simp [State.setAll, State.set?_eq_update, after, hStart, Scalar.values]⟩)).mono
          (fun _ _ h => h) ?_
      rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
      have hy : reconstructedAttemptTuple (n, trials, time, alpha, dt, ⟨grid⟩) =
          reconstructedTryTuple (n, trials, ⟨grid⟩, ratio.value, dt) := by
        simp only [reconstructedAttemptTuple, reconstructedAttempt, hV, hR, reconstructedTryTuple,
          ite_true, ratio]
      rw [hy]
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive2 ⟨st, by
        simp [State.setAll, State.set?_eq_update, after, hStart, Scalar.values] at hst2
        simp [euler.reconstructedAttempt.ir, Expr.evalResults, Expr.eval, ← hst2, hStart,
          Scalar.values]⟩ hPost2
    · have hy : reconstructedAttemptTuple (n, trials, time, alpha, dt, ⟨grid⟩) =
          (9, 0.5 * dt, grid) := by
        simp only [reconstructedAttemptTuple, reconstructedAttempt, hV, hR, ite_true,
          Bool.false_eq_true, ite_false, ratio]
      rw [hy]
      let final := ((after.update 8 (.i64 9)).update 9 (.f64 (0.5 * dt).toBits)).update 10
        (.i64 pGrid)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet4, hGet5, final,
          F64Op.apply, F64Bits.toBits_mul, half_toBits], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive ⟨final, by
        simp [euler.reconstructedAttempt.ir, Expr.evalResults, Expr.eval, final, after, hStart,
          Scalar.values]⟩ fun ha => (hPre ha).2
  · have hy : reconstructedAttemptTuple (n, trials, time, alpha, dt, ⟨grid⟩) =
        (3, dt, grid) := by
      simp only [reconstructedAttemptTuple, reconstructedAttempt, hV, Bool.false_eq_true,
        ite_false]
    rw [hy]
    let final := ((after.update 8 (.i64 3)).update 9 (.f64 dt.toBits)).update 10 (.i64 pGrid)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, after, hStart, hGet4, hGet5, final], ?_⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive ⟨final, by
      simp [euler.reconstructedAttempt.ir, Expr.evalResults, Expr.eval, final, after, hStart,
        Scalar.values]⟩ fun ha => (hPre ha).2

theorem reconstructedAttempt_implements : Implements euler.module 51 reconstructedAttemptTuple :=
  (reconstructedAttempt_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

def reconstructedAdvanceWithTuple : UInt64 × UInt64 × Float × Float × Float ×
    Moved (Array Cell) → UInt64 × Float × Array Cell :=
  fun (n, trials, time, dt, alpha, grid) =>
    reconstructedAdvanceWith n trials time dt alpha grid.val

set_option maxHeartbeats 4000000 in
/-- Under `aborts = false`, the grid has `cells` cells, and the heap has room for two more
grids. -/
theorem reconstructedAdvanceWith_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 52 reconstructedAdvanceWithTuple
      (fun x heap store => aborts = false → x.2.2.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 50 euler.reconstructedAdvanceWith.ir
    "reconstructedAdvanceWith" rfl reconstructedAdvanceWithTuple _ _
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl,
        rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, trials, time, dt, alpha, ⟨grid⟩⟩ heap initial _ hHeap hPre
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
  let s3 := s2.update 8 (.i64 pGrid)
  have hS3 : s3.params.length + s3.locals.length = 14 := by simp [s3, s2, hStart]
  have hT : ∀ j, j < 6 → s3.get j = start.get j := fun j hj => by
    simp only [s3, s2]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega),
      State.get_update_ne (by omega)]
  show TripleA _ _ (.seq (.assign 6 (.const 9)) (.seq (.assign 7 (.getF 3))
    (.seq (.assign 8 (.get 5)) (.seq (Stmt.repeatWhile [6, 7, 8] 9 10 (.const 2048)
      ((Expr.get 6).eq (.const 9)) 51 _) _)))) 14 _ _
  refine Stmt.seq_run ⟨start.update 6 (.i64 9), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet3, s2], ?_⟩
  refine Stmt.seq_run ⟨s3, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hGet5, s2, s3], ?_⟩
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ :=
    reconstructedAdvanceWith_loop n trials time dt alpha grid
  let F : UInt64 × Float × Array Cell → UInt64 × UInt64 × Float × Float × Float ×
      Moved (Array Cell) := fun x => (n, trials, time, alpha, x.2.1, ⟨x.2.2⟩)
  let Hold : UInt64 × Float × Array Cell → Heap → Store Unit → Prop := fun x heap s =>
    aborts = false → x.2.2.size = cells ∧ heap.Bounded s euler.module g (spare + 2) pages
  have hSmall := hg.cells
  refine Stmt.seq_spec (Live.repeatWhileOneA (reconstructedAttempt_implementsA hg spare pages)
    rfl rfl rfl (by decide) (by decide) (by omega)
    (n := 2048) ⟨s3, by simp [Expr.eval]⟩ cond step F (fun x => (hStepEq x).symm) Hold
    (fun x _ _ _ _ hH _ hP ha => ⟨by
      rw [hStepEq]
      exact (reconstructedAttempt_size n trials time alpha x.2.1 x.2.2
        (by have := (hH ha).1; omega)).trans (hH ha).1, hP ha⟩)
    (x0 := ((9 : UInt64), dt, grid)) (p0 := pGrid) hLive
    (by
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
      · simp [s3, s2, hStart]
      · simp [s3, s2, hStart]
      · simp [s3, s2, hStart])
    hPre hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have h6 : st.get 6 = some (.i64 a) := by
      simp [State.Holds, Scalar.values] at hHolds
      exact hHolds.1
    exact ⟨st, by simp [Expr.eval, h6, hCondEq]⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hHoldX hFrame
    have hG : ∀ j, j < 6 → st.get j = start.get j := fun j hj =>
      (hFrame.get j (by omega) (by simp; omega)).trans (hT j hj)
    have hH : st.get 6 = some (.i64 a) ∧ st.get 7 = some (.f64 b.toBits) ∧
        st.get 8 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_cons_self ..)
    refine ⟨[.i64 n, .i64 trials, .f64 time.toBits, .f64 alpha.toBits, .f64 b.toBits, .i64 p],
      st, ?_, ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p,
        rfl, hOld⟩, hHoldX, rfl, fun q hq => by simp [Represent.reads] at hq⟩
    simp [Expr.evalResults, Expr.eval, hG 0 (by decide), hG 1 (by decide), hG 2 (by decide),
      hG 4 (by decide), hH.2.1, hH.2.2, hGet0, hGet1, hGet2, hGet4]
  · apply TripleA.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4, hHold4⟩
    generalize hR : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step = R
      at hL4 hHolds4 hHold4
    obtain ⟨a, b, c⟩ := R
    have hy : reconstructedAdvanceWithTuple (n, trials, time, dt, alpha, ⟨grid⟩) =
        (if a == 0 then ((0 : UInt64), time + b, c)
        else (if a == 9 then 4 else a, time, c)) := by
      show reconstructedAdvanceWith n trials time dt alpha grid = _
      rw [hDef, hR]
    rw [hy]
    have hLen4 : st4.params.length + st4.locals.length = 14 := by
      rw [hFrame4.params, hFrame4.locals]; exact hS3
    have hG : ∀ j, j < 6 → st4.get j = start.get j := fun j hj =>
      (hFrame4.get j (by omega) (by simp; omega)).trans (hT j hj)
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
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL4 ⟨final, by
        simp [euler.reconstructedAdvanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4,
          Scalar.values]⟩ fun ha => (hHold4 ha).2
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 11 (.i64 (if a == 9 then 4 else a))).update 12
        (.f64 time.toBits)).update 13 (.i64 p4)
      refine Stmt.seq_run ⟨st4.update 11 (.i64 (if a == 9 then 4 else a)), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1], ?_⟩
      refine Stmt.seq_run ⟨(st4.update 11 (.i64 (if a == 9 then 4 else a))).update 12
          (.f64 time.toBits), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hG 2 (by decide), hGet2], ?_⟩
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL4 ⟨final, by
        simp [euler.reconstructedAdvanceWith.ir, Expr.evalResults, Expr.eval, final, hLen4,
          Scalar.values]⟩ fun ha => (hHold4 ha).2

theorem reconstructedAdvanceWith_implements :
    Implements euler.module 52 reconstructedAdvanceWithTuple :=
  (reconstructedAdvanceWith_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩
    0 0).implements_of fun _ _ _ h => nomatch h

def reconstructedAdvanceStepTuple : UInt64 × UInt64 × Float × Moved (Array Cell) →
    UInt64 × Float × Array Cell :=
  fun (n, trials, time, grid) => reconstructedAdvanceStep n trials time grid.val

set_option maxHeartbeats 4000000 in
/-- Under `aborts = false`, the grid has `cells` cells, and the heap has room for two more
grids. -/
theorem reconstructedAdvanceStep_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 53 reconstructedAdvanceStepTuple
      (fun x heap store => aborts = false → x.2.2.2.val.size = cells ∧
        heap.Bounded store euler.module g (spare + 2) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_movesA euler.funcs 51 euler.reconstructedAdvanceStep.ir
    "reconstructedAdvanceStep" rfl reconstructedAdvanceStepTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, trials, time, ⟨grid⟩⟩ heap initial _ hHeap hPre
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
  show TripleA _ _ (.seq (.call 48 [⟨.u64, .get 3⟩] [4, 5]) _) 11 _ _
  refine Live.callScalar_seqA gridUpper_implementsA rfl rfl rfl hLive hCap (x := grid)
    (before := start) (afterArgs := start) (after := after)
    (by simp [Expr.evalResults, Expr.eval, hGet3])
    ⟨pGrid, rfl, (hLive.tempsOwned (pGrid, flatWords grid) (by simp)).borrowed⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, hStart, after, Scalar.values, Flat.flat,
      stats]) ?_
  rintro heap1 s1 hLive1 ⟨rfl, rfl⟩
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
    refine (Live.callOneA (reconstructedAdvanceWith_implementsA hg spare pages) rfl rfl rfl
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
        hLive1.tempsOwned (pGrid, flatWords grid) (by simp)⟩ hPre
      rfl (fun r hr => by simp [Represent.reads] at hr)
      (fun q => ⟨((s10.update 8 (.i64 q)).update 7
          (.f64 (reconstructedAdvanceWithTuple (n, trials, time, proposal n time stats.value,
            stats.value, ⟨grid⟩)).2.1.toBits)).update 6
          (.i64 (reconstructedAdvanceWithTuple (n, trials, time, proposal n time stats.value,
            stats.value, ⟨grid⟩)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, s10, s9, after, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, s10, s9, after, Scalar.values] at hst2
      simp [euler.reconstructedAdvanceStep.ir, Expr.evalResults, Expr.eval, ← hst2, hStart,
        Scalar.values]⟩ hPost2
  · have hy : reconstructedAdvanceStepTuple (n, trials, time, ⟨grid⟩) = (2, time, grid) := by
      simp only [reconstructedAdvanceStepTuple, reconstructedAdvanceStep, hS, Bool.false_eq_true,
        ite_false, stats]
    rw [hy]
    let final := ((after.update 6 (.i64 2)).update 7 (.f64 time.toBits)).update 8 (.i64 pGrid)
    refine Stmt.run_triple ⟨final, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, after, hGet2, hGet3, final], ?_⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive1 ⟨final, by
      simp [euler.reconstructedAdvanceStep.ir, Expr.evalResults, Expr.eval, final, after, hStart,
        Scalar.values]⟩ fun ha => (hPre ha).2

theorem reconstructedAdvanceStep_implements :
    Implements euler.module 53 reconstructedAdvanceStepTuple :=
  (reconstructedAdvanceStep_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩
    0 0).implements_of fun _ _ _ h => nomatch h

def reconstructedRunFromTuple : UInt64 × UInt64 → UInt64 × Float × Array Cell :=
  fun (n, trials) => reconstructedRunFrom n trials

def reconstructedRunTuple : UInt64 × UInt64 → UInt64 × Float × Array Cell :=
  fun (n, trials) => reconstructedRun n trials

def reconstructedSolveTuple : UInt64 × UInt64 → Array UInt64 :=
  fun (n, trials) => reconstructedSolve n trials

set_option maxHeartbeats 4000000 in
/-- Under `aborts = false`, `n * n` is `cells`, and the heap has room for three more grids. -/
theorem reconstructedRunFrom_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 54 reconstructedRunFromTuple
      (fun x heap store => aborts = false → (x.1 * x.1).toNat = cells ∧
        heap.Bounded store euler.module g (spare + 3) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_heapA euler.funcs 52 euler.reconstructedRunFrom.ir "reconstructedRunFrom"
    rfl reconstructedRunFromTuple _ _ (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨n, trials⟩ heap initial _ hHeap hPre rfl hCap
  set start := euler.reconstructedRunFrom.ir.state (Scalar.values (n, trials)) with hStartDef
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  let s2 := (start.update 2 (.i64 0)).update 3 (.f64 0)
  show TripleA _ _ (.seq (.assign 2 (.const 0)) (.seq (.assign 3 (.constF 0))
    (.seq (.call 10 [⟨.u64, .get 0⟩] [4]) (.seq (Stmt.repeatWhile [2, 3, 4] 5 6
      (.const 4294967296) _ 53 _) _)))) 10 _ _
  refine Stmt.seq_run ⟨start.update 2 (.i64 0), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
  refine Live.callOne_seqA (initialCells_implementsA hg (spare + 2) pages) rfl rfl rfl
    (consumed := []) (Live.start hHeap)
    hCap (x := n) (vals := [.i64 n]) (before := s2) (afterArgs := s2)
    (by simp [Expr.evalResults, Expr.eval, s2, hGet0]) rfl hPre rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨s2.update 4 (.i64 q), by simp [State.setAll, State.set?_eq_update, s2, hStart]⟩) ?_
  intro heap1 p1 s3 st3 hLive1 hst3 hPost1
  have hst : st3 = s2.update 4 (.i64 p1) := by
    simp [State.setAll, State.set?_eq_update, s2, hStart] at hst3
    exact hst3.symm
  subst hst
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := reconstructedRunFrom_loop n trials
  let F : UInt64 × Float × Array Cell → UInt64 × UInt64 × Float × Moved (Array Cell) :=
    fun x => (n, trials, x.2.1, ⟨x.2.2⟩)
  have hS3 : (s2.update 4 (.i64 p1)).params.length + (s2.update 4 (.i64 p1)).locals.length = 10 :=
    by simp [s2, hStart]
  let Hold : UInt64 × Float × Array Cell → Heap → Store Unit → Prop := fun x heap s =>
    aborts = false → x.2.2.size = cells ∧ heap.Bounded s euler.module g (spare + 2) pages
  have hSmall := hg.cells
  refine Stmt.seq_spec (Live.repeatWhileOneA (reconstructedAdvanceStep_implementsA hg spare pages)
    rfl rfl rfl (by decide) (by decide) (by omega) (n := 4294967296)
    ⟨s2.update 4 (.i64 p1), by simp [Expr.eval]⟩
    cond step F (fun x => (hStepEq x).symm) Hold
    (fun x _ _ _ _ hH _ hP ha => ⟨by
      rw [hStepEq]
      exact (reconstructedAdvanceStep_size (by have := (hH ha).1; omega)).trans (hH ha).1,
      hP ha⟩)
    (x0 := ((0 : UInt64), (0 : Float), initialCells n)) (p0 := p1) hLive1
    (by simp [State.Holds, s2, hStart, Scalar.values, zero_toBits])
    (fun ha => ⟨(initialCells_size n).trans (hPre ha).1, hPost1 ha⟩) hCap (fun _ => rfl) ?_ ?_) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have hH : st.get 2 = some (.i64 a) ∧ st.get 3 = some (.f64 b.toBits) := by
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
    have hG1 : st.get 1 = some (.i64 trials) :=
      (hFrame.get 1 (by omega) (by simp)).trans (by simp [s2, hGet1])
    have hH : st.get 2 = some (.i64 a) ∧ st.get 3 = some (.f64 b.toBits) ∧
        st.get 4 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_singleton_self _)
    have hF : F (a, b, c) = (n, trials, b, ⟨c⟩) := rfl
    rw [hF]
    refine ⟨[.i64 n, .i64 trials, .f64 b.toBits, .i64 p], st, ?_,
      ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOld⟩, hHoldX, rfl,
      fun q hq => by simp [Represent.reads] at hq⟩
    simp [Expr.evalResults, Expr.eval, hG0, hG1, hH.2.1, hH.2.2]
  · apply TripleA.of_forall
    rintro s4 st4 ⟨heap4, p4, hL4, hHolds4, hFrame4, hHold4⟩
    generalize hR : LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n)
      cond step = R at hL4 hHolds4 hHold4
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
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages)
        (y := ((5 : UInt64), b, c)) hL4 ⟨final, by
          simp [euler.reconstructedRunFrom.ir, Expr.evalResults, Expr.eval, final, hLen4,
            Scalar.values]⟩ fun ha => (hHold4 ha).2
    · simp only [hA, Bool.false_eq_true, ite_false]
      let final := ((st4.update 7 (.i64 a)).update 8 (.f64 b.toBits)).update 9 (.i64 p4)
      refine Stmt.run_triple ⟨final, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen4, hH.1, hH.2.1, hH.2.2, final], ?_⟩
      exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hL4 ⟨final, by
        simp [euler.reconstructedRunFrom.ir, Expr.evalResults, Expr.eval, final, hLen4,
          Scalar.values]⟩ fun ha => (hHold4 ha).2

theorem reconstructedRunFrom_implements : Implements euler.module 54 reconstructedRunFromTuple :=
  (reconstructedRunFrom_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

set_option maxHeartbeats 2000000 in
/-- Under `aborts = false`, `n * n` is `cells` when `n` is in range, and the heap has room for
three more grids. -/
theorem reconstructedRun_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 55 reconstructedRunTuple
      (fun x heap store => aborts = false →
        ((2 ≤ x.1 && x.1 ≤ 800) = true → (x.1 * x.1).toNat = cells) ∧
        heap.Bounded store euler.module g (spare + 3) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 2) pages) := by
  refine Func.implements_heapA euler.funcs 53 euler.reconstructedRun.ir "reconstructedRun" rfl
    reconstructedRunTuple _ _ (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨n, trials⟩ heap initial _ hHeap hPre rfl hCap
  set start := euler.reconstructedRun.ir.state (Scalar.values (n, trials)) with hStartDef
  have hStart : start.params.length + start.locals.length = 5 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  show TripleA _ _ (.ite _ (.call 54 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3, 4])
    (.seq (.assign 2 (.const 1)) (.seq (.assign 3 (.constF 0)) (Stmt.arrayLiteral 4 [])))) 5 _ _
  refine Stmt.ite_test (b := 2 ≤ n && n ≤ 800)
    (by simp [Expr.eval, hGet0, word_and, word_beq_one, U64Op.apply]) (fun hN => ?_)
    (fun hN => ?_)
  · have hy : reconstructedRunTuple (n, trials) = reconstructedRunFromTuple (n, trials) := by
      simp [reconstructedRunTuple, reconstructedRun, reconstructedRunFromTuple, hN]
    rw [hy]
    refine (Live.callOneA (reconstructedRunFrom_implementsA hg spare pages) rfl rfl rfl
      (consumed := []) (Live.start hHeap) hCap (x := (n, trials)) (vals := [.i64 n, .i64 trials])
      (before := start) (afterArgs := start)
      (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1]) rfl
      (fun ha => ⟨(hPre ha).1 hN, (hPre ha).2⟩) rfl (fun _ _ _ h => nomatch h)
      (fun q => ⟨((start.update 4 (.i64 q)).update 3
          (.f64 (reconstructedRunFromTuple (n, trials)).2.1.toBits)).update 2
          (.i64 (reconstructedRunFromTuple (n, trials)).1), by
        simp [State.setAll, State.set?_eq_update, hStart, Scalar.values]⟩)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, ptr2, hLive2, hst2, hPost2⟩
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages) hLive2 ⟨st, by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values] at hst2
      simp [euler.reconstructedRun.ir, Expr.evalResults, Expr.eval, ← hst2, hStart,
        Scalar.values]⟩ hPost2
  · have hy : reconstructedRunTuple (n, trials) = (1, 0, #[]) := by
      simp [reconstructedRunTuple, reconstructedRun, hN]
    rw [hy]
    let s2 := (start.update 2 (.i64 1)).update 3 (.f64 0)
    refine Stmt.seq_run ⟨start.update 2 (.i64 1), by
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
    have hLen : st.params.length + st.locals.length = 5 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, hStart]
    have hG : ∀ j, j < 4 → st.get j = s2.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    exact Live.finish_results_oneP (P := Spare aborts g (spare + 2) pages)
      (y := ((1 : UInt64), (0 : Float), (#[] : Array Cell)))
      (Live.push (Live.start hHeap) hNew) ⟨st, by
        simp [euler.reconstructedRun.ir, Expr.evalResults, Expr.eval, hP, hG 2 (by decide),
          hG 3 (by decide), s2, hStart, Scalar.values, zero_toBits]⟩
      fun ha => (hPre ha).2.allocate hHeap hNeed hg.eight hCap hPages hNew.caps

theorem reconstructedRun_implements : Implements euler.module 55 reconstructedRunTuple :=
  (reconstructedRun_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

/-- The grid of a reconstructed run has at most `cells` cells when `n * n` is `cells` for `n` in
range. -/
theorem reconstructedRun_grid_size (n trials : UInt64) {cells : Nat}
    (h : (2 ≤ n && n ≤ 800) = true → (n * n).toNat = cells) :
    (reconstructedRun n trials).2.2.size ≤ cells := by
  unfold reconstructedRun
  split
  · rename_i hn
    rw [reconstructedRunFrom_size, h hn]
  · simp

set_option maxHeartbeats 2000000 in
/-- Under `aborts = false`, `n * n` is `cells` when `n` is in range, `cells` is positive, and the
heap has room for three more grids. -/
theorem reconstructedSolve_implementsA {aborts : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA aborts euler.module 56 reconstructedSolveTuple
      (fun x heap store => aborts = false →
        ((2 ≤ x.1 && x.1 ≤ 800) = true → (x.1 * x.1).toNat = cells) ∧ 1 ≤ cells ∧
        heap.Bounded store euler.module g (spare + 3) pages)
      (fun _ _ _ heap' final => aborts = false →
        heap'.Bounded final euler.module g (spare + 1) pages) := by
  refine Func.implements_heapA euler.funcs 54 euler.reconstructedSolve.ir "reconstructedSolve" rfl
    reconstructedSolveTuple _ _ (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨n, trials⟩ heap initial _ hHeap hPre rfl hCap
  set start := euler.reconstructedSolve.ir.state (Scalar.values (n, trials)) with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 trials) := rfl
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      reconstructedRun n trials = (status, time, grid) := ⟨_, _, _, rfl⟩
  have hGridSize : aborts = false → grid.size ≤ cells := fun ha => by
    have := reconstructedRun_grid_size n trials (hPre ha).1
    rw [hRun] at this
    exact this
  have hy : reconstructedSolveTuple (n, trials) = packTuple (n, status, time, grid) := by
    simp [reconstructedSolveTuple, reconstructedSolve, hRun, packTuple]
  rw [hy]
  show TripleA _ _ (.seq (.call 55 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3, 4])
    (.seq (.call 22 _ [5]) (.seq (.assign 6 (.get 5)) (.call 1 [⟨.u64, .get 4⟩] [])))) 7 _ _
  refine Live.callOne_seqA (reconstructedRun_implementsA hg spare pages) rfl rfl rfl
    (consumed := [])
    (Live.start hHeap) hCap (x := (n, trials)) (vals := [.i64 n, .i64 trials]) (before := start)
    (afterArgs := start) (by simp [Expr.evalResults, Expr.eval, hGet0, hGet1]) rfl
    (fun ha => ⟨(hPre ha).1, (hPre ha).2.2⟩) rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨((start.update 4 (.i64 q)).update 3 (.f64 time.toBits)).update 2 (.i64 status), by
      simp [State.setAll, State.set?_eq_update, hStart, Scalar.values, reconstructedRunTuple,
        hRun]⟩) ?_
  intro heap1 pg s2 st2 hLive1 hst2 hPost1
  have hst : st2 = ((start.update 4 (.i64 pg)).update 3 (.f64 time.toBits)).update 2
      (.i64 status) := by
    simp [State.setAll, State.set?_eq_update, hStart, Scalar.values, reconstructedRunTuple,
      hRun] at hst2
    exact hst2.symm
  subst hst
  simp only [reconstructedRunTuple, hRun] at hLive1
  let s3 := ((start.update 4 (.i64 pg)).update 3 (.f64 time.toBits)).update 2 (.i64 status)
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
    (fun q => ⟨s3.update 5 (.i64 q), by simp [State.setAll, State.set?_eq_update, hStart, s3]⟩) ?_
  intro heap2 pk s4 st4 hLive2 hst4 hPost2
  have hst : st4 = s3.update 5 (.i64 pk) := by
    simp [State.setAll, State.set?_eq_update, hStart, s3] at hst4
    exact hst4.symm
  subst hst
  let final := (s3.update 5 (.i64 pk)).update 6 (.i64 pk)
  refine Stmt.seq_run ⟨final, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s3, final], ?_⟩
  exact Live.releaseSecond_last_pages hLive2 rfl rfl (by simp [final, s3, hStart])
    fun s hL hPages => Live.finish_results_oneP (P := Spare aborts g (spare + 1) pages) hL
      ⟨final, by
        simp [euler.reconstructedSolve.ir, Expr.evalResults, Expr.eval, final, s3, hStart]⟩
      fun ha => (hPost2 ha).release hLive2.at_ (hLive2.tempsOwned (pg, flatWords grid) (by simp))
        hPages (hL.caps.trans hLive2.caps.symm)

theorem reconstructedSolve_implements : Implements euler.module 56 reconstructedSolveTuple :=
  (reconstructedSolve_implementsA (aborts := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

end Examples.Euler
