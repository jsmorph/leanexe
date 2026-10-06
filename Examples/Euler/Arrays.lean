import Examples.Euler.Kernels
import LeanExe.IR.BuildRecord
import LeanExe.Pipeline.Budget

/-! The compiled functions of the first-order Euler solver that build and read arrays of cells
compute their Lean definitions.  An array of cells is stored as `flatWords`, six words for each
cell: the four conserved components, the pressure, and the status. -/

namespace Examples.Euler

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime LeanExe.ProofKit Examples.Euler

theorem cell_length (c : Cell) : (Scalar.values c).length = 6 := rfl

/-- `g` is the byte count of an array of `cells` cells, whose words a build allows. -/
structure GridBytes (cells : Nat) (g : UInt64) : Prop where
  bytes : g.toNat = 8 * (cells * 6 + 1)
  cells : cells ≤ 536870911 / 6

theorem GridBytes.eight {cells : Nat} {g : UInt64} (h : GridBytes cells g) : 8 ≤ g.toNat := by
  have := h.bytes
  omega

/-- Under `a = false`, the heap has room for `spare` more blocks of `g` bytes within `pages`
pages. -/
abbrev Spare (a : Bool) (g : UInt64) (spare pages : Nat) (heap : Heap) (store : Store Unit) :
    Prop :=
  a = false → heap.Bounded store euler.module g spare pages

/-- The allocation of an array of `cells` cells has `g` bytes. -/
theorem GridBytes.need {cells : Nat} {g : UInt64} (h : GridBytes cells g) {count : UInt64}
    (hCount : count.toNat = cells) : UInt64.ofNat (8 * (count.toNat * 6 + 1)) = g := by
  have := h.bytes
  have := h.cells
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [hCount, UInt64.size]; omega), hCount]
  omega

theorem GridBytes.need_le {cells : Nat} {g : UInt64} (h : GridBytes cells g) {count : UInt64}
    (hCount : count.toNat = cells) : UInt64.ofNat (8 * (count.toNat * 6 + 1)) ≤ g :=
  UInt64.le_iff_toNat_le.mpr (Nat.le_of_eq (congrArg UInt64.toNat (h.need hCount)))

/-- The words of a pack of an array of `size` cells, `4 + 2 size` of them, fit in `g` bytes. -/
theorem pack_need {size : Nat} {g : UInt64} (hFit : 8 * (2 * size + 5) ≤ g.toNat)
    (hSize : size < 536870912) :
    UInt64.ofNat (8 * ((4 + 2 * size.toUInt64).toNat + 1)) ≤ g := by
  have := g.toNat_lt
  have hs : size.toUInt64.toNat = size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  have h2 : (4 + 2 * size.toUInt64).toNat = 4 + 2 * size := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hs]
    simp only [UInt64.reduceToNat, UInt64.size]
    omega
  rw [UInt64.le_iff_toNat_le, h2, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  omega

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
/-- Under `a = false`, `n * n` is `cells`, and the heap has room for one more grid. -/
theorem initialCells_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 10 initialCells
      (fun n heap store => a = false → (n * n).toNat = cells ∧
        heap.Bounded store euler.module g (spare + 1) pages)
      (fun _ _ _ heap' final => a = false → heap'.Bounded final euler.module g spare pages) := by
  refine Func.implements_heapA euler.funcs 8 euler.initialCells.ir "initialCells" rfl initialCells
    _ _ (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap hPre rfl hCap
  have hI := initialCell_implements (a := a)
  refine (Stmt.buildRecords_specA (writes := [4, 5, 6, 7, 8, 9]) (n := n * n) (scratch := 10)
    (elements := [.toBits (.getF 4), .toBits (.getF 5), .toBits (.getF 6), .toBits (.getF 7),
      .toBits (.getF 8), .get 9])
    (before := euler.initialCells.ir.state (Scalar.values n)) (initialCell n) cell_length
    (by decide) rfl rfl rfl (by decide) (by decide) (by decide) (Nat.le_of_eq rfl) hHeap hCap
    (fun ha => by rw [(hPre ha).1]; exact hg.cells)
    (fun ha => (hPre ha).2.room hHeap (by omega) (hg.need_le (hPre ha).1) hg.eight hCap)
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
  rintro store state ⟨ptr, -, hPtr, hNew, hPages⟩
  exact ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [euler.initialCells.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, hNew.owned⟩, hNew.keeps,
    fun ha => (hPre ha).2.allocate hHeap (hg.need_le (hPre ha).1) hg.eight hCap hPages hNew.caps⟩

theorem initialCells_implements : Implements euler.module 10 initialCells :=
  (initialCells_implementsA (a := true) (cells := 0) (g := 8) ⟨rfl, by decide⟩ 0 0).implements_of
    fun _ _ _ h => nomatch h

end Examples.Euler
