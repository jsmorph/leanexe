import Examples.Euler.Reconstruct
import Examples.Euler.Steps

/-! The compiled grid functions of the reconstructed Euler solver compute their Lean
definitions. -/

namespace Examples.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Euler

def cellUpperTuple : Float × Float × Float × Float → Checked :=
  fun (rho, mx, my, energy) => cellUpper rho mx my energy

set_option maxHeartbeats 2000000 in
theorem cellUpper_implements {a : Bool} : ImplementsPureA a euler.module 47 cellUpperTuple :=
  Func.implementsPureA euler.funcs 45 euler.cellUpper.ir "cellUpper" rfl cellUpperTuple
    (fun _ => rfl) fun ⟨rho, mx, my, energy⟩ initial => by
      refine Stmt.seq_callPure speedUpper_implements rfl rfl rfl (x := (rho, mx, my, energy)) ?_
      eval_ir [euler.cellUpper.ir, speedUpperTuple]
      refine Stmt.seq_callPure speedUpper_implements rfl rfl rfl (x := (rho, my, mx, energy)) ?_
      eval_ir [speedUpperTuple]
      refine Stmt.run_triple ?_
      eval_ir [cellUpperTuple, cellUpper, mergeChecked, rejectedChecked, word_and, word_eq_one,
        toBits_ite]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h, toBits_ite]
      · eval_ir [h, zero_toBits, and_assoc]

def gridRatioTuple : UInt64 × Float × Float → Checked :=
  fun (n, dt, alpha) => gridRatio n dt alpha

set_option maxHeartbeats 2000000 in
theorem gridRatio_implements {a : Bool} : ImplementsPureA a euler.module 49 gridRatioTuple :=
  Func.implementsPureA euler.funcs 47 euler.gridRatio.ir "gridRatio" rfl gridRatioTuple
    (fun _ => rfl) fun ⟨n, dt, alpha⟩ initial => by
      let spacing := outDiv false 1 n.toFloat
      let ratio := outDiv true dt spacing.value
      refine Stmt.seq_callPure outDiv_implements rfl rfl rfl (x := (false, 1, n.toFloat)) ?_
      eval_ir [euler.gridRatio.ir, outDivTuple, one_toBits, F64Convert.toBits_toFloat]
      refine Stmt.seq_callPure outDiv_implements rfl rfl rfl (x := (true, dt, spacing.value)) ?_
      eval_ir [outDivTuple, spacing]
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl (x := (true, ratio.value, alpha)) ?_
      eval_ir [outMulTuple, ratio, spacing]
      refine Stmt.run_triple ?_
      eval_ir [gridRatioTuple, gridRatio, positive, rejectedChecked, word_and, word_eq_one]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

/-- One step of `gridUpper`'s loop. -/
def gridUpperStep (grid : Array Cell) (i : UInt64) (acc : UInt64 × Float) : UInt64 × Float :=
  let q := grid[i.toNat]!.state
  let c := cellUpper q.density q.mx q.my q.energy
  (if acc.1 == 0 && c.status == 0 then 0 else 1,
    if acc.1 == 0 && c.status == 0 then
      (if acc.2.toBits ≤ c.value.toBits then c.value else acc.2)
    else 0)

set_option maxHeartbeats 4000000 in
theorem gridUpper_implementsA {a : Bool} :
    ImplementsA a euler.module 48 gridUpper (fun _ _ _ => True)
      (fun _ heap store heap' final => heap' = heap ∧ final = store) := by
  refine Func.implementsA euler.funcs 46 euler.gridUpper.ir "gridUpper" rfl gridUpper _
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro grid heap initial _ - - ⟨ptr, rfl, hGrid⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  have hSize : (flatWords grid).size < 536870912 := by have := hW.1; omega
  have hWords := flatWords_size cell_length grid
  set start := euler.gridUpper.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 17 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat (flatWords grid).size))
  let s2 := s1.update 2 (.i64 0)
  let s3 := s2.update 3 (.f64 0)
  show TripleA _ _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.const 0))
    (.seq (.assign 3 (.constF 0)) (.loop 4 5 (.bin .divU (.get 1) (.const 6)) _)))) 15 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3]
  have hS3 : s3.params.length + s3.locals.length = 17 := by simp [s3, s2, s1, hStart]
  refine (Stmt.loop_spec (vars := [2, 3]) (writes := 2 :: 3 :: (List.range 9).map (· + 6))
    (init := ((0 : UInt64), (0 : Float))) (n := grid.size.toUInt64) (gridUpperStep grid)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    ⟨(s3.update 15 (.i64 (UInt64.ofNat (flatWords grid).size))).update 16 (.i64 6),
      by simp [Expr.eval, s3, s2, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩
    (by simp [State.Holds, Scalar.values, s3, s2, s1, hStart, zero_toBits]) ?_).mono
      (fun _ _ h => h) ?_
  · rintro i ⟨status, speed⟩ state hi hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 17 := by
      rw [hFrame.params, hFrame.locals]; exact hS3
    have hS0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s3, s2, s1, hGet0])
    have hAcc : state.get 2 = some (.i64 status) ∧ state.get 3 = some (.f64 speed.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hi' : i < grid.size := by
      have : grid.size < 2 ^ 64 := by omega
      simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' this] using hi
    have hGuard : UInt64.ofNat i < 536870912 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp; omega
    have hRd : ∀ (j : Nat), j < 6 → ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * UInt64.ofNat 6 + UInt64.ofNat j) st =
          some (((Scalar.values grid[(UInt64.ofNat i).toNat]!).map Value.word)[j]!, st) :=
      fun j hj st h => Expr.readValue_record cell_length hj (by decide) cell_default hW hGuard h
    have hR0 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * 6) st =
          some (grid[(UInt64.ofNat i).toNat]!.state.density.toBits, st) :=
      fun st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 0 (by decide) st h
    have hR1 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * 6 + 1) st =
          some (grid[(UInt64.ofNat i).toNat]!.state.mx.toBits, st) :=
      fun st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 1 (by decide) st h
    have hR2 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * 6 + 2) st =
          some (grid[(UInt64.ofNat i).toNat]!.state.my.toBits, st) :=
      fun st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 2 (by decide) st h
    have hR3 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * 6 + 3) st =
          some (grid[(UInt64.ofNat i).toNat]!.state.energy.toBits, st) :=
      fun st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 3 (by decide) st h
    let q := grid[(UInt64.ofNat i).toNat]!.state
    iterate 5 (refine Stmt.seq_run ?_; eval_frame [hLength, hIndex, hS0, hGuard, hR0, hR1, hR2,
      hR3])
    refine Stmt.seq_callPure cellUpper_implements rfl rfl rfl
      (x := (q.density, q.mx, q.my, q.energy)) ?_
    eval_frame [hLength, q, cellUpperTuple]
    refine Stmt.run_triple ?_
    eval_frame [hLength, hAcc.1, hAcc.2, word_and, word_eq_one]
    refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, gridUpperStep, toBits_ite, zero_toBits]
  · rintro store state ⟨rfl, -, hHolds⟩
    refine ⟨rfl, _, state, ?_, rfl⟩
    have hLoop : gridUpper grid =
        ⟨(LeanExe.loop grid.size.toUInt64 ((0 : UInt64), (0 : Float)) (gridUpperStep grid)).1,
          (LeanExe.loop grid.size.toUInt64 ((0 : UInt64), (0 : Float)) (gridUpperStep grid)).2⟩ :=
      rfl
    have g : state.get 2 = some (.i64 (gridUpper grid).status) ∧
        state.get 3 = some (.f64 (gridUpper grid).value.toBits) := by
      rw [hLoop]
      simpa [State.Holds, Scalar.values] using hHolds
    simp [euler.gridUpper.ir, Func.scratch, Expr.evalResults, Expr.eval, g.1, g.2, Scalar.values,
      Flat.flat]

theorem gridUpper_implements : Implements euler.module 48 gridUpper :=
  (gridUpper_implementsA (a := true)).implements

/-- The lower neighbor and the far lower neighbor of a cell lie at or below it. -/
theorem lower_bounds (axisY : Bool) (i n : UInt64) (hi : i < 536870912) :
    (if (if axisY then i / n else i % n) = 0 then i else i - if axisY then n else 1) <
        536870912 ∧
      (if (if (if axisY then i / n else i % n) = 0 then (if axisY then i / n else i % n)
          else (if axisY then i / n else i % n) - 1) = 0 then
        (if (if axisY then i / n else i % n) = 0 then i else i - if axisY then n else 1)
      else (if (if axisY then i / n else i % n) = 0 then i else i - if axisY then n else 1) -
        if axisY then n else 1) < 536870912 := by
  have hiN : i.toNat < 536870912 := UInt64.lt_iff_toNat_lt.mp hi
  -- `s ≤ i` gives `i - s ≤ i` without wrapping.
  have sub_lt : ∀ a s : UInt64, s ≤ a → a.toNat < 536870912 → (a - s).toNat < 536870912 :=
    fun a s h ha => by rw [UInt64.toNat_sub_of_le _ _ h]; omega
  have lt_of : ∀ a : UInt64, a.toNat < 536870912 → a < 536870912 := fun a h =>
    UInt64.lt_iff_toNat_lt.mpr (by simpa using h)
  cases axisY
  · simp only [Bool.false_eq_true, ite_false]
    have hmod : (i % n).toNat = i.toNat % n.toNat := UInt64.toNat_mod _ _
    have hle : i.toNat % n.toNat ≤ i.toNat := Nat.mod_le _ _
    by_cases h0 : i % n = 0
    · simp only [h0, ite_true]
      exact ⟨hi, hi⟩
    · have hm : i.toNat % n.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [hmod, h]; rfl))
      have h1 : (1 : UInt64) ≤ i := UInt64.le_iff_toNat_le.mpr (by simp; omega)
      have hs : (i - 1).toNat = i.toNat - 1 := UInt64.toNat_sub_of_le _ _ h1
      simp only [h0, ite_false]
      refine ⟨lt_of _ (sub_lt _ _ h1 hiN), ?_⟩
      by_cases h2 : i % n - 1 = 0
      · simp only [h2, ite_true]
        exact lt_of _ (sub_lt _ _ h1 hiN)
      · have hm2 : i.toNat % n.toNat ≠ 1 := fun h => h2 (UInt64.toNat_inj.mp (by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), hmod, h]
          rfl))
        have h1' : (1 : UInt64) ≤ i - 1 := UInt64.le_iff_toNat_le.mpr (by rw [hs]; simp; omega)
        simp only [h2, ite_false]
        exact lt_of _ (sub_lt _ _ h1' (by rw [hs]; omega))
  · simp only [ite_true]
    have hdiv : (i / n).toNat = i.toNat / n.toNat := UInt64.toNat_div _ _
    have hmul : i.toNat / n.toNat * n.toNat ≤ i.toNat := Nat.div_mul_le_self _ _
    by_cases h0 : i / n = 0
    · simp only [h0, ite_true]
      exact ⟨hi, hi⟩
    · have hd : i.toNat / n.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [hdiv, h]; rfl))
      have hn1 : n.toNat ≤ i.toNat := by
        have := Nat.mul_le_mul_right n.toNat (Nat.one_le_iff_ne_zero.mpr hd)
        omega
      have hle : n ≤ i := UInt64.le_iff_toNat_le.mpr hn1
      have hs : (i - n).toNat = i.toNat - n.toNat := UInt64.toNat_sub_of_le _ _ hle
      simp only [h0, ite_false]
      refine ⟨lt_of _ (sub_lt _ _ hle hiN), ?_⟩
      by_cases h2 : i / n - 1 = 0
      · simp only [h2, ite_true]
        exact lt_of _ (sub_lt _ _ hle hiN)
      · have hd2 : 2 ≤ i.toNat / n.toNat := by
          by_contra hlt
          apply h2
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), hdiv]
          simp
          omega
        have hn2 : 2 * n.toNat ≤ i.toNat := by
          have := Nat.mul_le_mul_right n.toNat hd2
          omega
        have hle2 : n ≤ i - n := UInt64.le_iff_toNat_le.mpr (by rw [hs]; omega)
        simp only [h2, ite_false]
        exact lt_of _ (sub_lt _ _ hle2 (by rw [hs]; omega))

/-- Cell `index` of a reconstructed sweep. -/
def reconstructedSweepCell (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (index : UInt64) : Cell :=
  let cx := index % n
  let cy := index / n
  let coordinate := if axisY then cy else cx
  let stride := if axisY then n else 1
  let lower := if coordinate == 0 then index else index - stride
  let lowerCoordinate := if coordinate == 0 then coordinate else coordinate - 1
  let farLower := if lowerCoordinate == 0 then lower else lower - stride
  let upper := if coordinate + 1 < n then index + stride else index
  let upperCoordinate := if coordinate + 1 < n then coordinate + 1 else coordinate
  let farUpper := if upperCoordinate + 1 < n then upper + stride else upper
  let a := grid[farLower.toNat]!.state
  let b := grid[lower.toNat]!.state
  let c := grid[index.toNat]!.state
  let d := grid[upper.toNat]!.state
  let e := grid[farUpper.toNat]!.state
  let out := reconstructedStep trials ratio (oriented axisY a) (oriented axisY b)
    (oriented axisY c) (oriented axisY d) (oriented axisY e)
  ⟨⟨out.density, if axisY then out.transverse else out.momentum,
    if axisY then out.momentum else out.transverse, out.energy⟩, out.pressure, out.status⟩

theorem reconstructedSweep_build (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) : reconstructedSweep n axisY trials ratio grid =
      LeanExe.build grid.size.toUInt64 (reconstructedSweepCell n axisY trials ratio grid) :=
  rfl

def reconstructedSweepTuple : UInt64 × Bool × UInt64 × Float × Array Cell → Array Cell :=
  fun (n, axisY, trials, ratio, grid) => reconstructedSweep n axisY trials ratio grid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
/-- Under `a = false`, the grid has `cells` cells, and the heap has room for one more grid. -/
theorem reconstructedSweep_implementsA {a : Bool} {cells : Nat} {g : UInt64}
    (hg : GridBytes cells g) (spare pages : Nat) :
    ImplementsA a euler.module 44 reconstructedSweepTuple
      (fun x heap store => a = false → x.2.2.2.2.size = cells ∧
        heap.Bounded store euler.module g (spare + 1) pages)
      (fun _ _ _ heap' final => a = false → heap'.Bounded final euler.module g spare pages) := by
  refine Func.implements_heapA euler.funcs 42 euler.reconstructedSweep.ir "reconstructedSweep" rfl
    reconstructedSweepTuple _ _
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩
      rfl) ?_
  rintro ⟨n, axisY, trials, ratio, grid⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl, hGrid⟩ hCap
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  have hSize : (flatWords grid).size < 536870912 := by have := hW.1; omega
  have hW6 := flatWords_size cell_length grid
  have hCells : a = false → grid.size.toUInt64.toNat = cells := fun ha => by
    rw [← (hPre ha).1]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  set start := euler.reconstructedSweep.ir.state (Scalar.values n ++ (Scalar.values axisY ++
    (Scalar.values trials ++ (Scalar.values ratio ++ [.i64 ptr])))) with hStartDef
  let s1 := start.update 5 (.i64 (UInt64.ofNat (flatWords grid).size))
  have hStart : start.params.length + start.locals.length = 80 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 (cond axisY 1 0)) := rfl
  have hGet2 : start.get 2 = some (.i64 trials) := rfl
  have hGet3 : start.get 3 = some (.f64 ratio.toBits) := rfl
  have hGet4 : start.get 4 = some (.i64 ptr) := rfl
  show TripleA _ _ (.seq (.load .u64 5 (.get 4)) (Stmt.buildRecords 6 7 8
    (.bin .divU (.get 5) (.const 6)) _
    [.toBits (.getF 72), .toBits (.getF 73), .toBits (.getF 74), .toBits (.getF 75),
      .toBits (.getF 76), .get 77])) _ _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet4]
  rw [show reconstructedSweepTuple (n, axisY, trials, ratio, grid) = _ from
    reconstructedSweep_build n axisY trials ratio grid]
  refine (Stmt.buildRecords_specA (writes := (List.range 69).map (· + 9))
    (n := grid.size.toUInt64) (scratch := 78)
    (elements := [.toBits (.getF 72), .toBits (.getF 73), .toBits (.getF 74), .toBits (.getF 75),
      .toBits (.getF 76), .get 77])
    (before := s1) (reconstructedSweepCell n axisY trials ratio grid) cell_length (by decide) rfl
    rfl rfl (by decide)
    (by decide) (by decide) (by simp [s1, hStart]) hHeap hCap
    (fun _ => by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat', List.length_cons, List.length_nil]
      omega)
    (fun ha => (hPre ha).2.room hHeap (by omega) (hg.need_le (hCells ha)) hg.eight hCap)
    ⟨(s1.update 78 (.i64 (UInt64.ofNat (flatWords grid).size))).update 79 (.i64 6),
      by simp [Expr.eval, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 80 := by
      rw [hFrame.params, hFrame.locals]; simpa [s1] using hStart
    have hS0 : state.get 0 = some (.i64 n) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s1, hGet0])
    have hS1 : state.get 1 = some (.i64 (cond axisY 1 0)) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s1, hGet1])
    have hS2 : state.get 2 = some (.i64 trials) :=
      (hFrame.get 2 (by decide) (by decide)).trans (by simp [s1, hGet2])
    have hS3 : state.get 3 = some (.f64 ratio.toBits) :=
      (hFrame.get 3 (by decide) (by decide)).trans (by simp [s1, hGet3])
    have hS4 : state.get 4 = some (.i64 ptr) :=
      (hFrame.get 4 (by decide) (by decide)).trans (by simp [s1, hGet4])
    have hWords := flatWords_size cell_length grid
    have hi' : i < grid.size := by
      have : grid.size < 2 ^ 64 := by omega
      simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' this] using hi
    have hI : UInt64.ofNat i < 536870912 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp; omega
    have hX := hAt ptr _ hGrid
    have hRd : ∀ (j : Nat), j < 6 → ∀ (k : UInt64), k < 536870912 → ∀ st : State,
        st.get 4 = some (.i64 ptr) →
        Expr.readValue store.mem 4 (k * UInt64.ofNat 6 + UInt64.ofNat j) st =
          some (((Scalar.values grid[k.toNat]!).map Value.word)[j]!, st) :=
      fun j hj k hk st h => Expr.readValue_record cell_length hj (by decide) cell_default hX hk h
    have hR0 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 4 = some (.i64 ptr) →
        Expr.readValue store.mem 4 (k * 6) st = some (grid[k.toNat]!.state.density.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 0 (by decide) k hk st h
    have hR1 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 4 = some (.i64 ptr) →
        Expr.readValue store.mem 4 (k * 6 + 1) st = some (grid[k.toNat]!.state.mx.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 1 (by decide) k hk st h
    have hR2 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 4 = some (.i64 ptr) →
        Expr.readValue store.mem 4 (k * 6 + 2) st = some (grid[k.toNat]!.state.my.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 2 (by decide) k hk st h
    have hR3 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 4 = some (.i64 ptr) →
        Expr.readValue store.mem 4 (k * 6 + 3) st = some (grid[k.toNat]!.state.energy.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 3 (by decide) k hk st h
    have hZ : ∀ (k : UInt64), ¬k < 536870912 →
        grid[k.toNat]!.state.density.toBits = 0 ∧ grid[k.toNat]!.state.mx.toBits = 0 ∧
          grid[k.toNat]!.state.my.toBits = 0 ∧ grid[k.toNat]!.state.energy.toBits = 0 :=
      fun k hk => by
        have h := cell_words hSize k
        simp only [hk, ite_false] at h
        exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm⟩
    have hZ0 := fun k hk => (hZ k hk).1
    have hZ1 := fun k hk => (hZ k hk).2.1
    have hZ2 := fun k hk => (hZ k hk).2.2.1
    have hZ3 := fun k hk => (hZ k hk).2.2.2
    obtain ⟨hLower, hFarLower⟩ := lower_bounds axisY (UInt64.ofNat i) n hI
    let co := if axisY then UInt64.ofNat i / n else UInt64.ofNat i % n
    let st := if axisY then n else 1
    let lower := if co = 0 then UInt64.ofNat i else UInt64.ofNat i - st
    let lowerCo := if co = 0 then co else co - 1
    let farLower := if lowerCo = 0 then lower else lower - st
    let upper := if co + 1 < n then UInt64.ofNat i + st else UInt64.ofNat i
    let upperCo := if co + 1 < n then co + 1 else co
    let farUpper := if upperCo + 1 < n then upper + st else upper
    let qa := grid[farLower.toNat]!.state
    let qb := grid[lower.toNat]!.state
    let qc := grid[(UInt64.ofNat i).toNat]!.state
    let qd := grid[upper.toNat]!.state
    let qe := grid[farUpper.toNat]!.state
    let x := (trials, ratio, oriented axisY qa, oriented axisY qb, oriented axisY qc,
      oriented axisY qd, oriented axisY qe)
    have hCell : reconstructedSweepCell n axisY trials ratio grid (UInt64.ofNat i) =
        ⟨⟨(reconstructedStepTuple x).density,
          if axisY then (reconstructedStepTuple x).transverse
          else (reconstructedStepTuple x).momentum,
          if axisY then (reconstructedStepTuple x).momentum
          else (reconstructedStepTuple x).transverse,
          (reconstructedStepTuple x).energy⟩, (reconstructedStepTuple x).pressure,
          (reconstructedStepTuple x).status⟩ := by
      simp only [reconstructedSweepCell, beq_iff_eq]
      rfl
    rw [hCell]
    by_cases hU : upper < 536870912 <;> by_cases hFU : farUpper < 536870912
    all_goals
      simp only [upper, upperCo, farUpper, co, st] at hU hFU
      iterate 35 (refine Stmt.seq_run ?_; eval_frame [hLength, hIndex, hS0, hS1, hS2, hS3, hS4,
        hI, hLower, hFarLower, hU, hFU, hR0, hR1, hR2, hR3])
      iterate 20 (refine Stmt.seq_run ?_; eval_frame [hLength, hS1])
      refine Stmt.seq_callPure reconstructedStep_implements rfl rfl rfl (x := x) ?_
      eval_frame [hLength, hS1, hS2, hS3, hU, hFU, hZ0, hZ1, hZ2, hZ3, x, qa, qb, qc, qd, qe,
        farLower, lower, lowerCo, upper, upperCo, farUpper, co, st, oriented, toBits_ite]
      refine Stmt.run_triple ?_
      eval_frame [hLength, hS1]
      refine ⟨?_, fun j hj => ?_⟩
      · repeat refine State.Frame.update ?_ (by decide)
        exact State.Frame.refl _ _ _
      · obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
          omega
        all_goals
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some, Value.word]
        rotate_left 5
        exact Expr.yields_get (by simp [hLength])
        all_goals exact Expr.yields_toBits (by simp [hLength])
  rintro store state ⟨ptr, -, hPtr, hNew, hPages⟩
  exact ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [euler.reconstructedSweep.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, hNew.owned⟩, hNew.keeps,
    fun ha => (hPre ha).2.allocate hHeap (hg.need_le (hCells ha)) hg.eight hCap hPages hNew.caps⟩

theorem reconstructedSweep_implements : Implements euler.module 44 reconstructedSweepTuple :=
  (reconstructedSweep_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0
    ).implements_of fun _ _ _ h => nomatch h

end Examples.Euler
