import Project.Euler.Reconstruct
import Project.Euler.Steps

/-! The compiled grid functions of the reconstructed Euler solver compute their Lean
definitions. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

def cellUpperTuple : Float × Float × Float × Float → Checked :=
  fun (rho, mx, my, energy) => cellUpper rho mx my energy

set_option maxHeartbeats 2000000 in
theorem cellUpper_implements : ImplementsPure euler.module 47 cellUpperTuple :=
  Func.implementsPure euler.funcs 45 euler.cellUpper.ir "cellUpper" rfl cellUpperTuple
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
theorem gridRatio_implements : ImplementsPure euler.module 49 gridRatioTuple :=
  Func.implementsPure euler.funcs 47 euler.gridRatio.ir "gridRatio" rfl gridRatioTuple
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
theorem gridUpper_implements : Implements euler.module 48 gridUpper := by
  refine Func.implements euler.funcs 46 euler.gridUpper.ir "gridUpper" rfl gridUpper
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro grid heap initial _ - ⟨ptr, rfl, hGrid⟩
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
  show Triple _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.const 0))
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

end Project.Euler
