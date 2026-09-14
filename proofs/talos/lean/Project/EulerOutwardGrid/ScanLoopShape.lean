import Project.EulerOutwardGrid.Cell
import Project.EulerRiemann.Memory

namespace Project.EulerOutwardGrid.Execution
open Wasm
open Project.EulerRiemann
open Project.ProofKit.F64Outward (Checked)
open Project.EulerOutwardSpeed.Execution (checkedValues)

def scanLoop : Wasm.Program :=
  match (func45[25]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem scan_loop_shape :
    func45[25]? = some (.block 0 0 [.loop 0 0 scanLoop]) := rfl

structure ScanScratch where
  cell : Traversal.Cell := ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩
  previous : Checked := ⟨0, 0⟩
  borrowed : UInt64 := 0
  visited : UInt64 := 0

def scanFrame (pointer : UInt64) (count index : Nat)
    (acc : Checked) (scratch : ScanScratch) : Locals :=
  { params := [.i64 pointer]
    locals := [
      .i64 acc.status, .i64 acc.value,
      .i64 (UInt64.ofNat scratch.cell.index),
      .i64 scratch.cell.state.density, .i64 scratch.cell.state.mx,
      .i64 scratch.cell.state.my, .i64 scratch.cell.state.energy,
      .i64 scratch.cell.pressure, .i64 scratch.cell.status,
      .i64 scratch.previous.status, .i64 scratch.previous.value,
      .i64 (UInt64.ofNat scratch.cell.index),
      .i64 scratch.cell.state.density, .i64 scratch.cell.state.mx,
      .i64 scratch.cell.state.my, .i64 scratch.cell.state.energy,
      .i64 scratch.cell.pressure, .i64 scratch.cell.status,
      .i64 acc.status, .i64 acc.value, .i64 acc.status, .i64 acc.value,
      .i64 0, .i64 0,
      .i64 pointer, .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat count),
      .i64 scratch.borrowed, .i64 acc.status, .i64 acc.value, .i64 scratch.visited,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def scanPrefix (grid : Array Traversal.Cell) (index : Nat) : Checked :=
  Project.ProofKit.ArrayFold.foldPrefix grid OutwardMaximum.scanCell ⟨0, 0⟩ index

theorem scanPrefix_zero (grid : Array Traversal.Cell) :
    scanPrefix grid 0 = ⟨0, 0⟩ := by
  simp [scanPrefix, Project.ProofKit.ArrayFold.foldPrefix]

theorem scanPrefix_succ (grid : Array Traversal.Cell)
    (index : Nat) (hi : index < grid.size) :
    scanPrefix grid (index + 1) = OutwardMaximum.scanCell (scanPrefix grid index) grid[index] :=
  Project.ProofKit.ArrayFold.foldPrefix_succ grid OutwardMaximum.scanCell ⟨0, 0⟩ index hi

theorem scanPrefix_size (grid : Array Traversal.Cell) :
    scanPrefix grid grid.size = OutwardMaximum.gridUpper grid :=
  Project.ProofKit.ArrayFold.foldPrefix_size grid OutwardMaximum.scanCell ⟨0, 0⟩

def scanInvariant (initial : Store Unit) (pointer : UInt64)
    (grid : Array Traversal.Cell) : AssertionF Unit :=
  fun current frame => current = initial ∧
    ∃ (index : Nat) (scratch : ScanScratch),
      index ≤ grid.size ∧
      frame = scanFrame pointer grid.size index (scanPrefix grid index) scratch

def scanMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 27 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

theorem scanMeasure_frame (count index : Nat) (initial : Store Unit)
    (pointer : UInt64) (acc : Checked) (scratch : ScanScratch)
    (hi : index < UInt64.size) :
    scanMeasure count initial (scanFrame pointer count index acc scratch) =
      count - index + 1 := by
  simp [scanMeasure, scanFrame, Locals.get, UInt64.toNat_ofNat_of_lt' hi]

#print axioms scan_loop_shape
#print axioms scanPrefix_succ
#print axioms scanPrefix_size
#print axioms scanMeasure_frame

end Project.EulerOutwardGrid.Execution
