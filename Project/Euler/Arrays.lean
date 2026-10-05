import Project.Euler.Kernels
import Project.IR.BuildRecord

/-! The compiled functions of the first-order Euler solver that build and read arrays of cells
compute their Lean definitions.  An array of cells is stored as `flatWords`, six words for each
cell: the four conserved components, the pressure, and the status. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

theorem cell_length (c : Cell) : (Scalar.values c).length = 6 := rfl

theorem cell_default : (Scalar.values (default : Cell)).map Value.word = List.replicate 6 0 := by
  simp only [Scalar.values, Flat.flat, Value.word, List.map, List.cons_append, List.nil_append]
  rw [show (default : Cell) = ⟨⟨default, default, default, default⟩, default, 0⟩ from rfl]
  simp [zero_toBits, show (default : Float) = 0 from rfl]

/-- The guarded reads of the six words of cell `k`, in the form the evaluation of a compiled
body produces. -/
theorem cell_words {grid : Array Cell} (hSize : (flatWords grid).size < 536870912) (k : UInt64) :
    (if k < 536870912 then (flatWords grid)[(k * 6).toNat]! else 0) =
        grid[k.toNat]!.state.density.toBits ∧
      (if k < 536870912 then (flatWords grid)[(k * 6 + 1).toNat]! else 0) =
        grid[k.toNat]!.state.mx.toBits ∧
      (if k < 536870912 then (flatWords grid)[(k * 6 + 2).toNat]! else 0) =
        grid[k.toNat]!.state.my.toBits ∧
      (if k < 536870912 then (flatWords grid)[(k * 6 + 3).toNat]! else 0) =
        grid[k.toNat]!.state.energy.toBits ∧
      (if k < 536870912 then (flatWords grid)[(k * 6 + 4).toNat]! else 0) =
        grid[k.toNat]!.pressure.toBits ∧
      (if k < 536870912 then (flatWords grid)[(k * 6 + 5).toNat]! else 0) =
        grid[k.toNat]!.status := by
  have h := fun (j : Nat) (hj : j < 6) =>
    flatWords_read cell_length (j := j) hj (by decide) cell_default hSize k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Scalar.values, Flat.flat, Value.word] using h 0 (by decide)
  · simpa [Scalar.values, Flat.flat, Value.word] using h 1 (by decide)
  · simpa [Scalar.values, Flat.flat, Value.word] using h 2 (by decide)
  · simpa [Scalar.values, Flat.flat, Value.word] using h 3 (by decide)
  · simpa [Scalar.values, Flat.flat, Value.word] using h 4 (by decide)
  · simpa [Scalar.values, Flat.flat, Value.word] using h 5 (by decide)

set_option maxHeartbeats 4000000 in
theorem initialCells_implements : Implements euler.module 10 initialCells := by
  refine Func.implements_heap euler.funcs 8 euler.initialCells.ir "initialCells" rfl initialCells
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap rfl hCap
  have hI := initialCell_implements
  refine (Stmt.buildRecords_spec (writes := [4, 5, 6, 7, 8, 9]) (n := n * n) (scratch := 10)
    (elements := [.toBits (.getF 4), .toBits (.getF 5), .toBits (.getF 6), .toBits (.getF 7),
      .toBits (.getF 8), .get 9])
    (before := euler.initialCells.ir.state (Scalar.values n)) (initialCell n) cell_length
    (by decide) rfl rfl rfl (by decide) (by decide) (by decide) (Nat.le_of_eq rfl) hHeap hCap
    ⟨euler.initialCells.ir.state (Scalar.values n), rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 10 := by
      rw [hFrame.params, hFrame.locals]; rfl
    have h0 : state.get 0 = some (.i64 n) :=
      (hFrame.get 0 (by decide) (by decide)).trans rfl
    refine Stmt.callPure_last hI rfl rfl rfl (x := (n, UInt64.ofNat i)) ?_
    simp [Expr.evalResults, Expr.eval, h0, hIndex, Scalar.values, State.setAll,
      State.set?_eq_update, hLength, initialCellTuple]
    refine ⟨?_, fun j hj => ?_⟩
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
        omega
      all_goals
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, Value.word]
        first
          | exact Expr.yields_toBits (by simp [hLength])
          | exact Expr.yields_get (by simp [hLength])
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [euler.initialCells.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  exact hNew.owned

end Project.Euler
