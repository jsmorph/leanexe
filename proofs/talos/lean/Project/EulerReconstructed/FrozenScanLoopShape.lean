import Project.EulerReconstructed.FrozenScalars
import Project.EulerOutwardGrid.ScanLoopShape
import Project.EulerRiemann.FrozenMemory

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm
open Project.EulerRiemann.Frozen
open Project.ProofKit.F64Outward (Checked)
open Project.EulerOutwardGrid.Execution (ScanScratch)

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

def scanLoop : Wasm.Program :=
  match (func46[25]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem scan_loop_shape :
    func46[25]? = some (.block 0 0 [.loop 0 0 scanLoop]) := rfl

def scanFrame (owner pointer : UInt64) (count index : Nat)
    (acc : Checked) (scratch : ScanScratch) : Locals :=
  { Project.EulerOutwardGrid.Execution.scanFrame pointer count index acc scratch with
    params := [.i64 owner, .i64 pointer] }

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
    (owner pointer : UInt64) (acc : Checked) (scratch : ScanScratch)
    (hi : index < UInt64.size) :
    scanMeasure count initial (scanFrame owner pointer count index acc scratch) =
      count - index + 1 := by
  simp [scanMeasure, scanFrame, Project.EulerOutwardGrid.Execution.scanFrame,
    Locals.get, UInt64.toNat_ofNat_of_lt' hi]

#print axioms scan_loop_shape
#print axioms scanMeasure_frame
end Project.EulerReconstructed.Frozen.Execution
