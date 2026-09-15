import Project.EulerReconstructed.TraversalHelpers
import Project.EulerReconstructed.Traversal

namespace Project.EulerReconstructed.Execution
open Wasm Project.Euler2DCellStep.Sweep
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell neighborIndex)
open Project.EulerRiemann.Execution (stateValues cellValues boolWord)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def stencilValues (input : Traversal.Stencil) : List Value :=
  stateValues input.farRight ++ stateValues input.right ++ stateValues input.center ++
    stateValues input.left ++ stateValues input.farLeft

macro "stencil_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func57Def, stateValues, cellValues, stencilValues, boolWord,
        Memory.cellWords, Array.getD, List.set,
        ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
        Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem cellStencil_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (axis : Bool) (owner pointer : UInt64)
    (grid : Array Cell) (cell : Cell)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hi : cell.index < n * n) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerReconstructed.«module» 57 initial
      (cellValues cell ++ [.i64 pointer, .i64 owner,
        .i64 (boolWord axis), .i64 (UInt64.ofNat n)])
      (fun final values => final = initial ∧
        values = stencilValues (Traversal.cellStencil n axis grid cell)) := by
  let left := neighborIndex n cell.index axis false
  let farLeft := neighborIndex n left axis false
  let right := neighborIndex n cell.index axis true
  let farRight := neighborIndex n right axis true
  have hl : left < n * n := Geometry.neighbor_lt n cell.index axis false (by omega) hi
  have hfl : farLeft < n * n := Geometry.neighbor_lt n left axis false (by omega) hl
  have hr : right < n * n := Geometry.neighbor_lt n cell.index axis true (by omega) hi
  have hfr : farRight < n * n := Geometry.neighbor_lt n right axis true (by omega) hr
  have hlSize : left < grid.size := by omega
  have hflSize : farLeft < grid.size := by omega
  have hrSize : right < grid.size := by omega
  have hfrSize : farRight < grid.size := by omega
  have hWord (i : Nat) (h : i < grid.size) :
      ¬ UInt64.ofNat (n * n) ≤ UInt64.ofNat i := by
    have hi64 : i < UInt64.size := lt_trans h hGrid.size_lt
    have hn64 : n * n < UInt64.size := by rw [← hSize]; exact hGrid.size_lt
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hi64,
      UInt64.toNat_ofNat_of_lt' hn64]
    omega
  have hlWord := hWord left hlSize
  have hflWord := hWord farLeft hflSize
  have hrWord := hWord right hrSize
  have hfrWord := hWord farRight hfrSize
  have hLength := hGrid.lengthRead
  have hLengthBound := Nat.not_lt.mpr hGrid.lengthBound
  have hOffset1 (i : Nat) : (UInt64.ofNat i * 7 + 2) * 8 =
      UInt64.ofNat (8 * (7 * i + 1 + 1)) := Memory.field_offset i 1
  have hBound1 (i : Nat) (h : i < grid.size) :=
    Nat.not_lt.mpr (hGrid.fieldBound i 1 h (by decide))
  have hRead1 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 1 h (by decide)
  have hOffset2 (i : Nat) : (UInt64.ofNat i * 7 + 3) * 8 =
      UInt64.ofNat (8 * (7 * i + 2 + 1)) := Memory.field_offset i 2
  have hBound2 (i : Nat) (h : i < grid.size) :=
    Nat.not_lt.mpr (hGrid.fieldBound i 2 h (by decide))
  have hRead2 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 2 h (by decide)
  have hOffset3 (i : Nat) : (UInt64.ofNat i * 7 + 4) * 8 =
      UInt64.ofNat (8 * (7 * i + 3 + 1)) := Memory.field_offset i 3
  have hBound3 (i : Nat) (h : i < grid.size) :=
    Nat.not_lt.mpr (hGrid.fieldBound i 3 h (by decide))
  have hRead3 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 3 h (by decide)
  have hOffset4 (i : Nat) : (UInt64.ofNat i * 7 + 5) * 8 =
      UInt64.ofNat (8 * (7 * i + 4 + 1)) := Memory.field_offset i 4
  have hBound4 (i : Nat) (h : i < grid.size) :=
    Nat.not_lt.mpr (hGrid.fieldBound i 4 h (by decide))
  have hRead4 (i : Nat) (h : i < grid.size) := hGrid.fieldRead i 4 h (by decide)
  have hLeftGet : grid[left]! = grid[left] := getElem!_pos grid left hlSize
  have hFarLeftGet : grid[farLeft]! = grid[farLeft] := getElem!_pos grid farLeft hflSize
  have hRightGet : grid[right]! = grid[right] := getElem!_pos grid right hrSize
  have hFarRightGet : grid[farRight]! = grid[farRight] := getElem!_pos grid farRight hfrSize
  unfold cellValues
  refine TerminatesWith.of_wp_entry_for (f := func57Def) rfl ?_ (by decide)
  change wp Project.EulerReconstructed.«module» func57 _ initial
    (func57Def.toLocals [.i64 (UInt64.ofNat n), .i64 (boolWord axis),
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat cell.index),
      .i64 cell.state.density, .i64 cell.state.mx, .i64 cell.state.my,
      .i64 cell.state.energy, .i64 cell.pressure, .i64 cell.status]) env
  unfold func57
  stencil_peel
  refine wp_call_tw (neighborIndex_exact env initial n cell.index axis false hn hi) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  stencil_peel
  refine wp_call_tw (neighborIndex_exact env initial n left axis false hn hl) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  stencil_peel
  refine wp_call_tw (neighborIndex_exact env initial n cell.index axis true hn hi) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  stencil_peel
  refine wp_call_tw (neighborIndex_exact env initial n right axis true hn hr) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  have hOrient := orient_exact env initial axis cell.state
  dsimp only [left, farLeft, right, farRight] at *
  cases axis
  all_goals
    stencil_peel
    refine wp_call_tw hOrient ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    stencil_peel
    simp [Traversal.cellStencil, hLeftGet, hFarLeftGet, hRightGet, hFarRightGet,
      left, farLeft, right, farRight, orient]

#print axioms cellStencil_exact
end Project.EulerReconstructed.Execution
