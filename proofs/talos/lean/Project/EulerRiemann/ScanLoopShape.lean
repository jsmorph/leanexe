import Project.EulerRiemann.ExecutionScanCell
import Project.EulerRiemann.Memory

namespace Project.EulerRiemann.Execution
open Wasm

def scanLoop : Wasm.Program :=
  match (func25[25]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem scan_loop_shape :
    func25[25]? = some (.block 0 0 [.loop 0 0 scanLoop]) := rfl

structure ScanScratch where
  cell : Traversal.Cell := ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩
  previous : Traversal.Scan := ⟨0, 0⟩
  borrowed : UInt64 := 0
  visited : UInt64 := 0

def scanFrame (owner pointer : UInt64) (count index : Nat)
    (acc : Traversal.Scan) (scratch : ScanScratch) : Locals :=
  { params := [.i64 owner, .i64 pointer]
    locals := [
      .i64 acc.status, .i64 acc.alpha,
      .i64 (UInt64.ofNat scratch.cell.index),
      .i64 scratch.cell.state.density, .i64 scratch.cell.state.mx,
      .i64 scratch.cell.state.my, .i64 scratch.cell.state.energy,
      .i64 scratch.cell.pressure, .i64 scratch.cell.status,
      .i64 scratch.previous.status, .i64 scratch.previous.alpha,
      .i64 (UInt64.ofNat scratch.cell.index),
      .i64 scratch.cell.state.density, .i64 scratch.cell.state.mx,
      .i64 scratch.cell.state.my, .i64 scratch.cell.state.energy,
      .i64 scratch.cell.pressure, .i64 scratch.cell.status,
      .i64 acc.status, .i64 acc.alpha, .i64 acc.status, .i64 acc.alpha,
      .i64 0, .i64 0,
      .i64 pointer, .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat count),
      .i64 scratch.borrowed, .i64 acc.status, .i64 acc.alpha, .i64 scratch.visited,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def scanPrefix (grid : Array Traversal.Cell) (index : Nat) : Traversal.Scan :=
  Project.ProofKit.ArrayFold.foldPrefix grid Traversal.scanCell ⟨0, 0⟩ index

theorem scanPrefix_zero (grid : Array Traversal.Cell) :
    scanPrefix grid 0 = ⟨0, 0⟩ := by
  simp [scanPrefix, Project.ProofKit.ArrayFold.foldPrefix]

theorem scanPrefix_succ (grid : Array Traversal.Cell)
    (index : Nat) (hi : index < grid.size) :
    scanPrefix grid (index + 1) = Traversal.scanCell (scanPrefix grid index) grid[index] :=
  Project.ProofKit.ArrayFold.foldPrefix_succ grid Traversal.scanCell ⟨0, 0⟩ index hi

theorem scanPrefix_size (grid : Array Traversal.Cell) :
    scanPrefix grid grid.size = Traversal.scan grid :=
  Project.ProofKit.ArrayFold.foldPrefix_size grid Traversal.scanCell ⟨0, 0⟩

def scanInvariant (initial : Store Unit) (owner pointer : UInt64)
    (grid : Array Traversal.Cell) : AssertionF Unit :=
  fun current frame => current = initial ∧
    ∃ (index : Nat) (scratch : ScanScratch),
      index ≤ grid.size ∧
      frame = scanFrame owner pointer grid.size index (scanPrefix grid index) scratch

def scanMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 28 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

theorem scanMeasure_frame (count index : Nat) (initial : Store Unit)
    (owner pointer : UInt64) (acc : Traversal.Scan) (scratch : ScanScratch)
    (hi : index < UInt64.size) :
    scanMeasure count initial (scanFrame owner pointer count index acc scratch) =
      count - index + 1 := by
  simp [scanMeasure, scanFrame, Locals.get, UInt64.toNat_ofNat_of_lt' hi]

#print axioms scan_loop_shape
#print axioms scanPrefix_succ
#print axioms scanPrefix_size
#print axioms scanMeasure_frame

end Project.EulerRiemann.Execution
