import Project.EulerRiemann.ExecutionNeighbor
import Project.EulerRiemann.Memory

namespace Project.EulerRiemann.Execution
open Wasm Project.Euler2DCellStep.Sweep

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def stateValues (state : State) : List Wasm.Value :=
  [.i64 state.energy, .i64 state.my, .i64 state.mx, .i64 state.density]

def cellValues (cell : Traversal.Cell) : List Wasm.Value :=
  [.i64 cell.status, .i64 cell.pressure, .i64 cell.state.energy,
    .i64 cell.state.my, .i64 cell.state.mx, .i64 cell.state.density,
    .i64 (UInt64.ofNat cell.index)]

def inputsValues (input : Inputs) : List Wasm.Value :=
  stateValues input.right ++ stateValues input.center ++ stateValues input.left

theorem orient_exact (env : HostEnv Unit) (initial : Store Unit)
    (axis : Bool) (state : State) :
    TerminatesWith env Project.EulerRiemann.«module» 32 initial
      (stateValues state ++ [.i64 (boolWord axis)])
      (fun final values => final = initial ∧ values = stateValues (orient axis state)) := by
  refine TerminatesWith.of_wp_entry_for (f := func32Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func32 _ initial
    (func32Def.toLocals [.i64 (boolWord axis), .i64 state.density,
      .i64 state.mx, .i64 state.my, .i64 state.energy]) env
  unfold func32
  cases axis
  all_goals
    repeat
      first
      | wp_run [func32Def, boolWord, List.set, List.getElem?_cons_zero,
          List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
      | refine wp_iff_cons rfl ?_
        conv => arg 2; simp [boolWord]
    simp [stateValues, orient]

macro "inputs_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func33Def, stateValues, cellValues, inputsValues,
        Memory.cellWords, Array.getD, List.set,
        ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
        Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, *]
    | refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem cellInputs_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (axis : Bool) (owner pointer : UInt64)
    (grid : Array Traversal.Cell) (cell : Traversal.Cell)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hi : cell.index < n * n) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerRiemann.«module» 33 initial
      (cellValues cell ++ [.i64 pointer, .i64 owner,
        .i64 (boolWord axis), .i64 (UInt64.ofNat n)])
      (fun final values => final = initial ∧
        values = inputsValues (Traversal.cellInputs n axis grid cell)) := by
  let left := Traversal.neighborIndex n cell.index axis false
  let right := Traversal.neighborIndex n cell.index axis true
  have hl : left < grid.size := by
    rw [hSize]
    exact Geometry.neighbor_lt n cell.index axis false (by omega) hi
  have hr : right < grid.size := by
    rw [hSize]
    exact Geometry.neighbor_lt n cell.index axis true (by omega) hi
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hGrid.size_lt
  have hlNat := UInt64.toNat_ofNat_of_lt' (show left < UInt64.size by have := hGrid.size_lt; omega)
  have hrNat := UInt64.toNat_ofNat_of_lt' (show right < UInt64.size by have := hGrid.size_lt; omega)
  have hlWord : UInt64.ofNat left < UInt64.ofNat grid.size := by
    simpa only [UInt64.lt_iff_toNat_lt, hlNat, hSizeNat] using hl
  have hrWord : UInt64.ofNat right < UInt64.ofNat grid.size := by
    simpa only [UInt64.lt_iff_toNat_lt, hrNat, hSizeNat] using hr
  have hlWordNot : ¬ UInt64.ofNat (n * n) ≤
      UInt64.ofNat (Traversal.neighborIndex n cell.index axis false) := by
    simpa only [left, hSize] using (UInt64.not_le.mpr hlWord)
  have hrWordNot : ¬ UInt64.ofNat (n * n) ≤
      UInt64.ofNat (Traversal.neighborIndex n cell.index axis true) := by
    simpa only [right, hSize] using (UInt64.not_le.mpr hrWord)
  have hlFull : Traversal.neighborIndex n cell.index axis false < n * n := by
    simpa only [left, hSize] using hl
  have hrFull : Traversal.neighborIndex n cell.index axis true < n * n := by
    simpa only [right, hSize] using hr
  have hLength := hGrid.lengthRead
  have hLengthBound := Nat.not_lt.mpr hGrid.lengthBound
  have hOffset1 (i : Nat) : (UInt64.ofNat i * 7 + 2) * 8 =
      UInt64.ofNat (8 * (7 * i + 1 + 1)) := Memory.field_offset i 1
  have hBound1 (i : Nat) (h : i < grid.size) := Nat.not_lt.mpr (hGrid.fieldBound i 1 h (by decide))
  have hRead1 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 1 h (by decide)
  have hOffset2 (i : Nat) : (UInt64.ofNat i * 7 + 3) * 8 =
      UInt64.ofNat (8 * (7 * i + 2 + 1)) := Memory.field_offset i 2
  have hBound2 (i : Nat) (h : i < grid.size) := Nat.not_lt.mpr (hGrid.fieldBound i 2 h (by decide))
  have hRead2 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 2 h (by decide)
  have hOffset3 (i : Nat) : (UInt64.ofNat i * 7 + 4) * 8 =
      UInt64.ofNat (8 * (7 * i + 3 + 1)) := Memory.field_offset i 3
  have hBound3 (i : Nat) (h : i < grid.size) := Nat.not_lt.mpr (hGrid.fieldBound i 3 h (by decide))
  have hRead3 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 3 h (by decide)
  have hOffset4 (i : Nat) : (UInt64.ofNat i * 7 + 5) * 8 =
      UInt64.ofNat (8 * (7 * i + 4 + 1)) := Memory.field_offset i 4
  have hBound4 (i : Nat) (h : i < grid.size) := Nat.not_lt.mpr (hGrid.fieldBound i 4 h (by decide))
  have hRead4 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 4 h (by decide)
  refine TerminatesWith.of_wp_entry_for (f := func33Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func33 _ initial
    (func33Def.toLocals [.i64 (UInt64.ofNat n), .i64 (boolWord axis),
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat cell.index),
      .i64 cell.state.density, .i64 cell.state.mx, .i64 cell.state.my,
      .i64 cell.state.energy, .i64 cell.pressure, .i64 cell.status]) env
  unfold func33
  inputs_peel
  refine wp_call_tw (neighborIndex_exact env initial n cell.index axis false hn hi) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  inputs_peel
  refine wp_call_tw (orient_exact env initial axis grid[left].state) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  inputs_peel
  refine wp_call_tw (orient_exact env initial axis cell.state) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  inputs_peel
  refine wp_call_tw (neighborIndex_exact env initial n cell.index axis true hn hi) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  inputs_peel
  refine wp_call_tw (orient_exact env initial axis grid[right].state) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  inputs_peel
  have hLeftGet : grid[Traversal.neighborIndex n cell.index axis false]! = grid[left] :=
    getElem!_pos grid left hl
  have hRightGet : grid[Traversal.neighborIndex n cell.index axis true]! = grid[right] :=
    getElem!_pos grid right hr
  simp [Traversal.cellInputs, hLeftGet, hRightGet]

#print axioms orient_exact
#print axioms cellInputs_exact

end Project.EulerRiemann.Execution
