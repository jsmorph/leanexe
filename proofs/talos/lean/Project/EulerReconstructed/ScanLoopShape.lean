import Project.EulerReconstructed.Scalars
import Project.EulerOutwardGrid.ScanLoopShape

namespace Project.EulerReconstructed.Execution
open Wasm
open Project.EulerRiemann
open Project.ProofKit.F64Outward (Checked)
open Project.EulerOutwardGrid.Execution (ScanScratch scanPrefix scanPrefix_zero
  scanPrefix_succ scanPrefix_size)

def scanLoop : Wasm.Program :=
  match (func46[23]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem scan_loop_shape :
    func46[23]? = some (.block 0 0 [.loop 0 0 scanLoop]) := rfl

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
end Project.EulerReconstructed.Execution
