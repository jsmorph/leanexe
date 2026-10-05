import Project.Euler.Arrays

/-! The compiled sweep of the first-order Euler solver computes its Lean definition. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

/-- `eval_ir` over an abstract state: the facts about its locals stay as hypotheses. -/
macro "eval_frame" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, State.set?_eq_update, State.setAll, U64Op.apply,
    F64Op.apply, F64UnOp.apply, Scalar.values, ScalarType.valueType, Expr.evalResults,
    ScalarType.value, Flat.flat, divU_eq, remU_eq, -mul_ite, -ite_mul, $args,*])

def sweepTuple : UInt64 × Bool × Float × Array Cell → Array Cell :=
  fun (n, axisY, ratio, grid) => sweep n axisY ratio grid

/-- Cell `index` of a sweep. -/
def sweepCell (n : UInt64) (axisY : Bool) (ratio : Float) (grid : Array Cell) (index : UInt64) :
    Cell :=
  let cx := index % n
  let cy := index / n
  let coordinate := if axisY then cy else cx
  let stride := if axisY then n else 1
  let lower := if coordinate == 0 then index else index - stride
  let upper := if coordinate + 1 < n then index + stride else index
  let l := grid[lower.toNat]!.state
  let c := grid[index.toNat]!.state
  let r := grid[upper.toNat]!.state
  let out := advanceCell ratio
    l.density (if axisY then l.my else l.mx) (if axisY then l.mx else l.my) l.energy
    c.density (if axisY then c.my else c.mx) (if axisY then c.mx else c.my) c.energy
    r.density (if axisY then r.my else r.mx) (if axisY then r.mx else r.my) r.energy
  ⟨⟨out.density, if axisY then out.transverse else out.momentum,
    if axisY then out.momentum else out.transverse, out.energy⟩, out.pressure, out.status⟩

theorem sweep_build (n : UInt64) (axisY : Bool) (ratio : Float) (grid : Array Cell) :
    sweep n axisY ratio grid = LeanExe.build grid.size.toUInt64 (sweepCell n axisY ratio grid) :=
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem sweep_implements : Implements euler.module 11 sweepTuple := by
  refine Func.implements_heap euler.funcs 9 euler.sweep.ir "sweep" rfl sweepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨n, axisY, ratio, grid⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, ptr, rfl, hGrid⟩ hCap
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  have hSize : (flatWords grid).size < 536870912 := by have := hW.1; omega
  have hA := advanceCell_implements
  set start := euler.sweep.ir.state
    (Scalar.values n ++ (Scalar.values axisY ++ (Scalar.values ratio ++ [.i64 ptr])))
    with hStartDef
  let s1 := start.update 4 (.i64 (UInt64.ofNat (flatWords grid).size))
  have hStart : start.params.length + start.locals.length = 45 := rfl
  have hGet0 : start.get 0 = some (.i64 n) := rfl
  have hGet1 : start.get 1 = some (.i64 (cond axisY 1 0)) := rfl
  have hGet2 : start.get 2 = some (.f64 ratio.toBits) := rfl
  have hGet3 : start.get 3 = some (.i64 ptr) := rfl
  show Triple _ (.seq (.load .u64 4 (.get 3)) (Stmt.buildRecords 5 6 7
    (.bin .divU (.get 4) (.const 6)) _
    [.toBits (.getF 37), .toBits (.getF 38), .toBits (.getF 39), .toBits (.getF 40),
      .toBits (.getF 41), .get 42])) _ _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet3]
  rw [show sweepTuple (n, axisY, ratio, grid) = _ from sweep_build n axisY ratio grid]
  refine (Stmt.buildRecords_spec (writes := (List.range 35).map (· + 8))
    (n := grid.size.toUInt64) (scratch := 43)
    (elements := [.toBits (.getF 37), .toBits (.getF 38), .toBits (.getF 39), .toBits (.getF 40),
      .toBits (.getF 41), .get 42])
    (before := s1) (sweepCell n axisY ratio grid) cell_length (by decide) rfl rfl rfl (by decide)
    (by decide) (by decide) (by simp [s1, hStart]) hHeap hCap
    ⟨(s1.update 43 (.i64 (UInt64.ofNat (flatWords grid).size))).update 44 (.i64 6),
      by simp [Expr.eval, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 45 := by
      rw [hFrame.params, hFrame.locals]; simpa [s1] using hStart
    have hS0 : state.get 0 = some (.i64 n) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s1, hGet0])
    have hS1 : state.get 1 = some (.i64 (cond axisY 1 0)) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s1, hGet1])
    have hS2 : state.get 2 = some (.f64 ratio.toBits) :=
      (hFrame.get 2 (by decide) (by decide)).trans (by simp [s1, hGet2])
    have hS3 : state.get 3 = some (.i64 ptr) :=
      (hFrame.get 3 (by decide) (by decide)).trans (by simp [s1, hGet3])
    have hX := hAt ptr _ hGrid
    have hWords := flatWords_size cell_length grid
    have hi' : i < grid.size := by
      have : grid.size < 2 ^ 64 := by omega
      simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' this] using hi
    have hI : UInt64.ofNat i < 536870912 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp; omega
    have hRd : ∀ (j : Nat), j < 6 → ∀ (k : UInt64), k < 536870912 → ∀ st : State,
        st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * UInt64.ofNat 6 + UInt64.ofNat j) st =
          some (((Scalar.values grid[k.toNat]!).map Value.word)[j]!, st) :=
      fun j hj k hk st h => Expr.readValue_record cell_length hj (by decide) cell_default hX hk h
    have hR0 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 6) st = some (grid[k.toNat]!.state.density.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 0 (by decide) k hk st h
    have hR1 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 6 + 1) st = some (grid[k.toNat]!.state.mx.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 1 (by decide) k hk st h
    have hR2 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 6 + 2) st = some (grid[k.toNat]!.state.my.toBits, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 2 (by decide) k hk st h
    have hR3 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 6 + 3) st = some (grid[k.toNat]!.state.energy.toBits, st) :=
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
    have hLower : (if (if axisY then UInt64.ofNat i / n else UInt64.ofNat i % n) = 0 then
        UInt64.ofNat i else UInt64.ofNat i - if axisY then n else 1) < 536870912 := by
      have hle : ∀ s : UInt64, s ≤ UInt64.ofNat i → UInt64.ofNat i - s < 536870912 :=
        fun s hs => by
          have h := UInt64.le_iff_toNat_le.mp (UInt64.sub_le hs)
          rw [UInt64.lt_iff_toNat_lt] at hI ⊢
          omega
      cases axisY
      · simp only [Bool.false_eq_true, ite_false]
        split
        · exact hI
        · rename_i h
          refine hle 1 (UInt64.le_iff_toNat_le.mpr ?_)
          have : (UInt64.ofNat i).toNat ≠ 0 := fun h0 =>
            h (by rw [← UInt64.toNat_inj, UInt64.toNat_mod, h0]; simp)
          simp only [UInt64.toNat_one]
          omega
      · simp only [ite_true]
        split
        · exact hI
        · rename_i h
          refine hle n (UInt64.le_iff_toNat_le.mpr (Nat.le_of_not_lt fun hlt => h ?_))
          rw [← UInt64.toNat_inj, UInt64.toNat_div, Nat.div_eq_of_lt hlt]
          rfl
    let lower := if (if axisY then UInt64.ofNat i / n else UInt64.ofNat i % n) = 0 then
      UInt64.ofNat i else UInt64.ofNat i - if axisY then n else 1
    let upper := if (if axisY then UInt64.ofNat i / n else UInt64.ofNat i % n) + 1 < n then
      UInt64.ofNat i + (if axisY then n else 1) else UInt64.ofNat i
    let l := grid[lower.toNat]!.state
    let c := grid[(UInt64.ofNat i).toNat]!.state
    let r := grid[upper.toNat]!.state
    let x := (ratio, l.density, if axisY then l.my else l.mx, if axisY then l.mx else l.my,
      l.energy, c.density, if axisY then c.my else c.mx, if axisY then c.mx else c.my, c.energy,
      r.density, if axisY then r.my else r.mx, if axisY then r.mx else r.my, r.energy)
    have hCell : sweepCell n axisY ratio grid (UInt64.ofNat i) =
        ⟨⟨(advanceCellTuple x).density,
          if axisY then (advanceCellTuple x).transverse else (advanceCellTuple x).momentum,
          if axisY then (advanceCellTuple x).momentum else (advanceCellTuple x).transverse,
          (advanceCellTuple x).energy⟩, (advanceCellTuple x).pressure,
          (advanceCellTuple x).status⟩ := by
      simp only [sweepCell, beq_iff_eq]
      rfl
    rw [hCell]
    by_cases hUpper : (if (if axisY then UInt64.ofNat i / n else UInt64.ofNat i % n) + 1 < n then
        UInt64.ofNat i + (if axisY then n else 1) else UInt64.ofNat i) < 536870912
    all_goals
      iterate 21 (refine Stmt.seq_run ?_; eval_frame [hLength, hIndex, hS0, hS1, hS2, hS3, hI,
        hLower, hUpper, hR0, hR1, hR2, hR3])
      refine Stmt.seq_callPure hA rfl rfl rfl (x := x) ?_
      eval_frame [hLength, hS1, hS2, hUpper, hZ0, hZ1, hZ2, hZ3, x, l, c, r, lower, upper,
        toBits_ite]
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
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [euler.sweep.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    hNew.keeps⟩
  exact hNew.owned

end Project.Euler
