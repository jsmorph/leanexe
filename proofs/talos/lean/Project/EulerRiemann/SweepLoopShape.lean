import Project.EulerRiemann.ExecutionUpdateCell
import Project.EulerRiemann.MemoryFrame
import Project.EulerRiemann.TraversalSweep

namespace Project.EulerRiemann.Execution
open Wasm

def sweepLoop : Wasm.Program :=
  match (func70[47]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem sweep_loop_shape :
    func70[47]? = some (.block 0 0 [.loop 0 0 sweepLoop]) := rfl

structure SweepScratch where
  cell : Traversal.Cell := ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩
  result : Traversal.Cell := ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩
  n : UInt64 := 0
  axis : UInt64 := 0
  ratio : UInt64 := 0
  owner : UInt64 := 0
  pointer : UInt64 := 0

def sweepFrame (n : Nat) (axis : Bool) (ratio owner source target : UInt64)
    (count index : Nat) (scratch : SweepScratch) (allocation : List Wasm.Value) : Locals :=
  { params := [.i64 (UInt64.ofNat n), .i64 (boolWord axis), .i64 ratio,
      .i64 owner, .i64 source]
    locals := [
      .i64 (UInt64.ofNat scratch.cell.index), .i64 scratch.cell.state.density,
      .i64 scratch.cell.state.mx, .i64 scratch.cell.state.my, .i64 scratch.cell.state.energy,
      .i64 scratch.cell.pressure, .i64 scratch.cell.status,
      .i64 scratch.n, .i64 scratch.axis, .i64 scratch.ratio, .i64 scratch.owner,
      .i64 scratch.pointer,
      .i64 (UInt64.ofNat scratch.cell.index), .i64 scratch.cell.state.density,
      .i64 scratch.cell.state.mx, .i64 scratch.cell.state.my, .i64 scratch.cell.state.energy,
      .i64 scratch.cell.pressure, .i64 scratch.cell.status,
      .i64 (UInt64.ofNat scratch.result.index), .i64 scratch.result.state.density,
      .i64 scratch.result.state.mx, .i64 scratch.result.state.my,
      .i64 scratch.result.state.energy, .i64 scratch.result.pressure, .i64 scratch.result.status,
      .i64 (UInt64.ofNat scratch.result.index), .i64 scratch.result.state.density,
      .i64 scratch.result.state.mx, .i64 scratch.result.state.my,
      .i64 scratch.result.state.energy, .i64 scratch.result.pressure, .i64 scratch.result.status,
      .i64 0, .i64 0, .i64 0,
      .i64 source, .i64 (UInt64.ofNat count), .i64 target, .i64 (UInt64.ofNat index)] ++ allocation
    values := [] }

def sweepInvariant (initial : Store Unit) (n : Nat) (axis : Bool)
    (ratio owner source target : UInt64) (grid : Array Traversal.Cell)
    (allocation : List Wasm.Value) : AssertionF Unit :=
  fun current frame =>
    Memory.GridAt current source grid ∧
    Memory.WritesGrid initial current target grid.size ∧
    ∃ (index : Nat) (scratch : SweepScratch),
      index ≤ grid.size ∧
      Memory.PrefixAt current target (Traversal.sweep n axis ratio grid) (7 * index) ∧
      frame = sweepFrame n axis ratio owner source target grid.size index scratch allocation

def sweepMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 44 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

theorem sweepMeasure_frame (count index n : Nat) (initial : Store Unit)
    (axis : Bool) (ratio owner source target : UInt64) (scratch : SweepScratch)
    (allocation : List Wasm.Value) (hAllocation : allocation.length = 8)
    (hi : index < UInt64.size) :
    sweepMeasure count initial
      (sweepFrame n axis ratio owner source target count index scratch allocation) =
      count - index + 1 := by
  simp [sweepMeasure, sweepFrame, Locals.get, hAllocation, UInt64.toNat_ofNat_of_lt' hi]

#print axioms sweep_loop_shape
#print axioms sweepMeasure_frame

end Project.EulerRiemann.Execution
