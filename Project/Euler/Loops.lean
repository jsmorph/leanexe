import Project.Euler.Sweep

/-! The compiled loops of the first-order Euler solver over a borrowed grid compute their Lean
definitions. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

/-- One step of `accepted`'s loop. -/
def acceptedStep (grid : Array Cell) (i : UInt64) (ok : Bool) : Bool :=
  ok && grid[i.toNat]!.status == 0

set_option maxHeartbeats 4000000 in
theorem accepted_implements : Implements euler.module 12 accepted := by
  refine Func.implements euler.funcs 10 euler.accepted.ir "accepted" rfl accepted
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro grid heap initial _ - ⟨ptr, rfl, hGrid⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  have hSize : (flatWords grid).size < 536870912 := by have := hW.1; omega
  have hWords := flatWords_size cell_length grid
  set start := euler.accepted.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat (flatWords grid).size))
  let s2 := s1.update 2 (.i64 1)
  show Triple _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.const 1))
    (.loop 3 4 (.bin .divU (.get 1) (.const 6)) _))) 8 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  have hS2 : s2.params.length + s2.locals.length = 10 := by simp [s2, s1, hStart]
  refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5, 6, 7]) (init := true)
    (n := grid.size.toUInt64) (acceptedStep grid) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega)
    ⟨(s2.update 8 (.i64 (UInt64.ofNat (flatWords grid).size))).update 9 (.i64 6),
      by simp [Expr.eval, s2, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩
    (by simp [State.Holds, Scalar.values, Flat.flat, s2, s1, hStart]) ?_).mono
      (fun _ _ h => h) ?_
  · intro i ok state hi hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 10 := by
      rw [hFrame.params, hFrame.locals]; exact hS2
    have hS0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have hOk : state.get 2 = some (.i64 (cond ok 1 0)) := by
      simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
    have hi' : i < grid.size := by
      have : grid.size < 2 ^ 64 := by omega
      simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' this] using hi
    have hGuard : UInt64.ofNat i < 536870912 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp; omega
    have hR5 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * 6 + 5) st =
          some (grid[(UInt64.ofNat i).toNat]!.status, st) :=
      fun st h0 => by
        have := Expr.readValue_record (j := 5) cell_length (by decide) (by decide)
          cell_default hW hGuard h0
        simpa [Scalar.values, Flat.flat, Value.word] using this
    refine Stmt.run_triple ?_
    eval_frame [hLength, hIndex, hS0, hOk, hGuard, hR5]
    refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, acceptedStep, word_and]
  · rintro store state ⟨rfl, -, hHolds⟩
    refine ⟨rfl, _, state, ?_, rfl⟩
    have g2 : state.get 2 = some (.i64 (cond (accepted grid) 1 0)) := by
      rw [show accepted grid = LeanExe.loop grid.size.toUInt64 true (acceptedStep grid) from rfl]
      simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
    simp [euler.accepted.ir, Func.scratch, Expr.evalResults, Expr.eval, g2, Scalar.values,
      Flat.flat]

/-- One step of `scan`'s loop. -/
def scanStep (grid : Array Cell) (i : UInt64) (acc : UInt64 × Float) : UInt64 × Float :=
  let q := grid[i.toNat]!.state
  let x := side q.density q.mx q.my q.energy
  let y := side q.density q.my q.mx q.energy
  let speed := if x.speed.toBits < y.speed.toBits then y.speed else x.speed
  (acc.1 ||| x.status ||| y.status, if acc.2.toBits < speed.toBits then speed else acc.2)

set_option maxHeartbeats 4000000 in
theorem scan_implements : Implements euler.module 15 scan := by
  refine Func.implements euler.funcs 13 euler.scan.ir "scan" rfl scan
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro grid heap initial _ - ⟨ptr, rfl, hGrid⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  have hSize : (flatWords grid).size < 536870912 := by have := hW.1; omega
  have hWords := flatWords_size cell_length grid
  have hS := side_implements
  set start := euler.scan.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 32 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat (flatWords grid).size))
  let s2 := s1.update 2 (.i64 0)
  let s3 := s2.update 3 (.f64 0)
  show Triple _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.const 0))
    (.seq (.assign 3 (.constF 0)) (.loop 4 5 (.bin .divU (.get 1) (.const 6)) _)))) 30 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3]
  have hS3 : s3.params.length + s3.locals.length = 32 := by simp [s3, s2, s1, hStart]
  refine (Stmt.loop_spec (vars := [2, 3]) (writes := 2 :: 3 :: (List.range 24).map (· + 6))
    (init := ((0 : UInt64), (0 : Float))) (n := grid.size.toUInt64) (scanStep grid)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    ⟨(s3.update 30 (.i64 (UInt64.ofNat (flatWords grid).size))).update 31 (.i64 6),
      by simp [Expr.eval, s3, s2, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩
    (by simp [State.Holds, Scalar.values, s3, s2, s1, hStart, zero_toBits]) ?_).mono
      (fun _ _ h => h) ?_
  · rintro i ⟨status, speed⟩ state hi hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 32 := by
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
    refine Stmt.seq_callPure hS rfl rfl rfl (x := (q.density, q.mx, q.my, q.energy)) ?_
    eval_frame [hLength, q, sideTuple]
    refine Stmt.seq_callPure hS rfl rfl rfl (x := (q.density, q.my, q.mx, q.energy)) ?_
    eval_frame [hLength, q, sideTuple]
    refine Stmt.run_triple ?_
    eval_frame [hLength, hAcc.1, hAcc.2]
    refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, scanStep, toBits_ite]
  · rintro store state ⟨rfl, -, hHolds⟩
    refine ⟨rfl, _, state, ?_, rfl⟩
    have g : state.get 2 = some (.i64 (scan grid).1) ∧
        state.get 3 = some (.f64 (scan grid).2.toBits) := by
      rw [show scan grid = LeanExe.loop grid.size.toUInt64 (0, 0) (scanStep grid) from rfl]
      simpa [State.Holds, Scalar.values] using hHolds
    simp [euler.scan.ir, Func.scratch, Expr.evalResults, Expr.eval, g.1, g.2, Scalar.values]

def packTuple : UInt64 × UInt64 × Float × Array Cell → Array UInt64 :=
  fun (n, status, time, grid) => pack n status time grid

/-- Word `i` of `pack`. -/
def packWord (n status : UInt64) (time : Float) (grid : Array Cell) (i : UInt64) : UInt64 :=
  if i == 0 then status else if i == 1 then time.toBits else if i < 4 then n
  else if i < 4 + grid.size.toUInt64 then grid[(i - 4).toNat]!.state.density.toBits
  else grid[(i - 4 - grid.size.toUInt64).toNat]!.pressure.toBits

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem pack_implements : Implements euler.module 22 packTuple := by
  refine Func.implements_heap euler.funcs 20 euler.pack.ir "pack" rfl packTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, status, time, grid⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl, hGrid⟩ hCap
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  have hSize : (flatWords grid).size < 536870912 := by have := hW.1; omega
  set start := euler.pack.ir.state
    (Scalar.values n ++ (Scalar.values status ++ (Scalar.values time ++ [.i64 ptr])))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 15 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 status) := rfl
  have hGet2 : start.get 2 = some (.f64 time.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 ptr) := rfl
  let k := grid.size.toUInt64
  let s1 := start.update 4 (.i64 (UInt64.ofNat (flatWords grid).size))
  let s2 := (((s1.update 13 (.i64 (UInt64.ofNat (flatWords grid).size))).update 14 (.i64 6)).update
    5 (.i64 k))
  show Triple _ (.seq (.load .u64 4 (.get 3)) (.seq (.assign 5 (.bin .divU (.get 4) (.const 6)))
    (Stmt.buildWith 6 7 8 (.bin .add (.const 4) (.bin .mul (.const 2) (.get 5))) _ _))) 13 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet3]
  · have hK : UInt64.ofNat (flatWords grid).size / 6 = k := hCount
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, U64Op.apply, hK]
  have hS2 : s2.params.length + s2.locals.length = 15 := by simp [s2, s1, hStart]
  rw [show packTuple (n, status, time, grid) = LeanExe.build (4 + 2 * k)
    (packWord n status time grid) from rfl]
  refine (Stmt.buildWith_spec (writes := [9, 10, 11, 12]) (n := 4 + 2 * k) (scratch := 13)
    (packWord n status time grid) rfl rfl rfl (by decide) (by decide) (by decide)
    (by omega) hHeap hCap
    (by simp [Expr.eval, s2, s1, hStart, U64Op.apply, State.set?_eq_update]) ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 15 := by
      rw [hFrame.params, hFrame.locals]; exact hS2
    have hS : ∀ j, j < 6 → state.get j = s2.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hS0 : state.get 0 = some (.i64 n) := (hS 0 (by decide)).trans (by simp [s2, s1, hGet0])
    have hS1 : state.get 1 = some (.i64 status) :=
      (hS 1 (by decide)).trans (by simp [s2, s1, hGet1])
    have hS2' : state.get 2 = some (.f64 time.toBits) :=
      (hS 2 (by decide)).trans (by simp [s2, s1, hGet2])
    have hS3 : state.get 3 = some (.i64 ptr) := (hS 3 (by decide)).trans (by simp [s2, s1, hGet3])
    have hS5 : state.get 5 = some (.i64 k) := (hS 5 (by decide)).trans (by simp [s2, s1, hStart])
    have hX := hAt ptr _ hGrid
    have hRd : ∀ (j : Nat), j < 6 → ∀ (c : UInt64), c < 536870912 → ∀ st : State,
        st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (c * UInt64.ofNat 6 + UInt64.ofNat j) st =
          some (((Scalar.values grid[c.toNat]!).map Value.word)[j]!, st) :=
      fun j hj c hc st h => Expr.readValue_record cell_length hj (by decide) cell_default hX hc h
    have hR0 : ∀ (c : UInt64), c < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (c * 6) st = some (grid[c.toNat]!.state.density.toBits, st) :=
      fun c hc st h => by
        simpa [Scalar.values, Flat.flat, Value.word] using hRd 0 (by decide) c hc st h
    have hR4 : ∀ (c : UInt64), c < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (c * 6 + 4) st = some (grid[c.toNat]!.pressure.toBits, st) :=
      fun c hc st h => by
        simpa [Scalar.values, Flat.flat, Value.word] using hRd 4 (by decide) c hc st h
    have hZ0 : ∀ (c : UInt64), ¬c < 536870912 → grid[c.toNat]!.state.density.toBits = 0 :=
      fun c hc => by
        have h := (cell_words hSize c).1
        simp only [hc, ite_false] at h
        exact h.symm
    have hZ4 : ∀ (c : UInt64), ¬c < 536870912 → grid[c.toNat]!.pressure.toBits = 0 :=
      fun c hc => by
        have h := (cell_words hSize c).2.2.2.2.1
        simp only [hc, ite_false] at h
        exact h.symm
    by_cases hD : UInt64.ofNat i - 4 < 536870912 <;>
    by_cases hP : UInt64.ofNat i - 4 - k < 536870912
    all_goals
      refine Stmt.run_triple ?_
      eval_frame [hLength, hIndex, hS0, hS1, hS2', hS3, hS5, hD, hP, hR0, hR4]
      refine ⟨?_, ?_⟩
      · repeat refine State.Frame.update ?_ (by decide)
        exact State.Frame.refl _ _ _
      · simp [hLength, packWord, k, hZ0, hZ4, hD, hP]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [euler.pack.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    hNew.keeps⟩
  exact hNew.owned

end Project.Euler
