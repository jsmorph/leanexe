import Project.Grids.Module
import Project.IR.Correct
import Project.IR.Run
import Project.IR.RecordRead
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

/-! The compiled reads of arrays of records compute their Lean definitions.  An array of `Cell`
is stored as `flatWords`, nine words for each cell, and `flatWords_read` gives each word the
compiled code reads. -/

namespace Project.Grids

open Project.Pipeline Project.IR Project.ProofKit LeanExe.Examples.Grids

instance : Flat Phase UInt64 := ⟨fun | .solid => 0 | .liquid => 1 | .gas => 2⟩
instance : Flat Conserved (Float × Float × Float × Float) :=
  ⟨fun s => (s.density, s.mx, s.my, s.energy)⟩
instance : Flat Cell (UInt64 × Conserved × Float × UInt64 × Bool × Phase) :=
  ⟨fun c => (c.index, c.state, c.pressure, c.status, c.ok, c.phase)⟩
instance : Flat Mass Float := ⟨Mass.value⟩

def densityTuple : Array Cell × UInt64 → Float := fun (g, i) => density g i
def pressureTuple : Array Cell × UInt64 → Float := fun (g, i) => pressure g i
def indexAtTuple : Array Cell × UInt64 → UInt64 := fun (g, i) => indexAt g i
def okAtTuple : Array Cell × UInt64 → Bool := fun (g, i) => okAt g i
def energySumTuple : Array Cell × UInt64 × UInt64 → Float := fun (g, i, j) => energySum g i j
def isGasTuple : Array Cell × UInt64 → Bool := fun (g, i) => isGas g i
def flagAtTuple : Array Bool × UInt64 → Bool := fun (xs, i) => flagAt xs i
def massAtTuple : Array Mass × UInt64 → Float := fun (xs, i) => massAt xs i

theorem zero_toBits : (default : Float).toBits = 0 := by
  change (UInt64.toFloat 0).toBits = 0
  rw [F64Convert.toBits_toFloat]
  decide +kernel

theorem cell_length (c : Cell) : (Scalar.values c).length = 9 := rfl

theorem cell_default : (Scalar.values (default : Cell)).map Value.word = List.replicate 9 0 := by
  simp only [Scalar.values, Flat.flat, Value.word, List.map, List.cons_append, List.nil_append]
  rw [show (default : Cell) = ⟨0, ⟨default, default, default, default⟩, default, 0, false, .solid⟩
    from rfl]
  simp [zero_toBits]

theorem bool_length (b : Bool) : (Scalar.values b).length = 1 := rfl

theorem bool_default : (Scalar.values (default : Bool)).map Value.word = [0] := rfl

theorem mass_length (x : Mass) : (Scalar.values x).length = 1 := rfl

theorem mass_default : (Scalar.values (default : Mass)).map Value.word = [0] := by
  simp only [Scalar.values, Flat.flat, Value.word, List.map]
  rw [show (default : Mass).value = default from rfl, zero_toBits]

/-- Evaluates a compiled body and its results, with the given lemmas. -/
macro "evaluate" "[" args:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? :
    tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
    Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get, State.update,
    U64Op.apply, F64Op.apply, Scalar.values, ScalarType.valueType, Expr.evalResults,
    ScalarType.value, Flat.flat, Value.word, $args,*] $[$loc]?)

/-- `hRead` gives component `j` of cell `i` of `grid`, laid out as `hW` states, read as the
compiled code reads it. -/
macro "cell_read" hRead:ident hW:ident grid:ident i:ident j:num : tactic =>
  `(tactic| have $hRead := flatWords_read cell_length (j := $j) (by decide) (by decide)
    cell_default (xs := $grid) (by have := ($hW).1; omega) $i)

theorem density_implements : Implements grids.module 2 densityTuple := by
  refine Func.implements grids.funcs 0 grids.density.ir "density" rfl densityTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 1
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.density.ir, Expr.readValue_at hW, densityTuple, density, hi] at hRead ⊢ <;>
    simpa using hRead

theorem pressure_implements : Implements grids.module 3 pressureTuple := by
  refine Func.implements grids.funcs 1 grids.pressure.ir "pressure" rfl pressureTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 5
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.pressure.ir, Expr.readValue_at hW, pressureTuple, pressure, hi] at hRead ⊢ <;>
    simpa using hRead

theorem indexAt_implements : Implements grids.module 4 indexAtTuple := by
  refine Func.implements grids.funcs 2 grids.indexAt.ir "indexAt" rfl indexAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 0
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.indexAt.ir, Expr.readValue_at hW, indexAtTuple, indexAt, hi] at hRead ⊢ <;>
    simpa using hRead

theorem okAt_implements : Implements grids.module 5 okAtTuple := by
  refine Func.implements grids.funcs 3 grids.okAt.ir "okAt" rfl okAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 7
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.okAt.ir, Expr.readValue_at hW, okAtTuple, okAt, hi] at hRead ⊢ <;>
    simpa using hRead

theorem count_implements : Implements grids.module 6 count := by
  refine Func.implements grids.funcs 4 grids.count.ir "count" rfl count
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro grid heap initial _ - ⟨ptr, rfl, hGrid⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  refine Stmt.run_triple ?_
  evaluate [grids.count.ir, hLength, hW.lengthRead, count]
  exact hCount

theorem energySum_implements : Implements grids.module 7 energySumTuple := by
  refine Func.implements grids.funcs 5 grids.energySum.ir "energySum" rfl energySumTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i, j⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead1 hW grid i 4
  cell_read hRead2 hW grid j 4
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;> by_cases hj : j < 536870912 <;>
    evaluate [grids.energySum.ir, Expr.readValue_at hW, energySumTuple, energySum, hi, hj,
      F64Bits.toBits_add] at hRead1 hRead2 ⊢ <;>
    rw [← hRead1, ← hRead2]

theorem isGas_implements : Implements grids.module 8 isGasTuple := by
  refine Func.implements grids.funcs 6 grids.isGas.ir "isGas" rfl isGasTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 8
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.isGas.ir, Expr.readValue_at hW, isGasTuple, isGas, hi] at hRead ⊢ <;>
    revert hRead <;> cases grid[i.toNat]!.phase <;> simp_all

theorem flagAt_implements : Implements grids.module 9 flagAtTuple := by
  refine Func.implements grids.funcs 7 grids.flagAt.ir "flagAt" rfl flagAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨flags, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hFlags⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords flags) at hFlags
  have hW := hFlags.values
  refine Stmt.run_triple ?_
  evaluate [grids.flagAt.ir, Expr.readValue_at hW, flagAtTuple, flagAt,
    flatWords_getElem!_one bool_length bool_default]

theorem flagCount_implements : Implements grids.module 10 flagCount := by
  refine Func.implements grids.funcs 8 grids.flagCount.ir "flagCount" rfl flagCount
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro flags heap initial _ - ⟨ptr, rfl, hFlags⟩
  change heap.Borrowed initial ptr (flatWords flags) at hFlags
  have hW := hFlags.values
  have hLength := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.run_triple ?_
  evaluate [grids.flagCount.ir, hLength, hW.lengthRead, flagCount, flatWords_size bool_length]

theorem massAt_implements : Implements grids.module 11 massAtTuple := by
  refine Func.implements grids.funcs 9 grids.massAt.ir "massAt" rfl massAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨masses, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hMasses⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords masses) at hMasses
  have hW := hMasses.values
  refine Stmt.run_triple ?_
  evaluate [grids.massAt.ir, Expr.readValue_at hW, massAtTuple, massAt,
    flatWords_getElem!_one mass_length mass_default]

/-- `encode` succeeds on `grids.module`, and its bytes decode to a module that computes each
function exactly. -/
theorem grids_bytes : ∃ bytes, Wasm.Encoding.encode grids.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 densityTuple ∧
      Implements m 3 pressureTuple ∧ Implements m 4 indexAtTuple ∧ Implements m 5 okAtTuple ∧
      Implements m 6 count ∧ Implements m 7 energySumTuple ∧ Implements m 8 isGasTuple ∧
      Implements m 9 flagAtTuple ∧ Implements m 10 flagCount ∧ Implements m 11 massAtTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip grids.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, grids.module, decoded, density_implements, pressure_implements,
    indexAt_implements, okAt_implements, count_implements, energySum_implements,
    isGas_implements, flagAt_implements, flagCount_implements, massAt_implements⟩

end Project.Grids
