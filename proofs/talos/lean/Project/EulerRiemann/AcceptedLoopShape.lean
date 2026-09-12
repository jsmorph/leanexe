import Project.EulerRiemann.Program
import Project.EulerRiemann.Memory
import Project.EulerRiemann.ExecutionNeighbor
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.EulerRiemann.Execution
open Wasm

def acceptedLoop : Wasm.Program :=
  match (func72[21]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem accepted_shape :
    func72 = func72.take 21 ++ [.block 0 0 [.loop 0 0 acceptedLoop]] ++ func72.drop 22 := rfl

def acceptedFrame (owner pointer : UInt64) (count index : Nat)
    (accepted : Bool) (cell : Traversal.Cell) : Locals :=
  { params := [.i64 owner, .i64 pointer]
    locals := [
      .i64 (UInt64.ofNat cell.index), .i64 cell.state.density, .i64 cell.state.mx,
      .i64 cell.state.my, .i64 cell.state.energy, .i64 cell.pressure, .i64 cell.status,
      .i64 0, .i64 pointer, .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat count), .i64 (boolWord accepted),
      .i64 pointer, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def acceptedPrefix (grid : Array Traversal.Cell) (index : Nat) : Prop :=
  ∀ (i : Nat) (hi : i < grid.size), i < index → grid[i].status = 0

def acceptedInvariant (initial : Store Unit) (owner pointer : UInt64)
    (grid : Array Traversal.Cell) : AssertionF Unit :=
  fun current frame => current = initial ∧
    ∃ (index : Nat) (cell : Traversal.Cell),
      index ≤ grid.size ∧ acceptedPrefix grid index ∧
      frame = acceptedFrame owner pointer grid.size index true cell

def acceptedMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 12 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

theorem acceptedPrefix_complete (grid : Array Traversal.Cell)
    (h : acceptedPrefix grid grid.size) : Traversal.accepted grid = true := by
  simp only [Traversal.accepted, Array.all_eq_true, beq_iff_eq]
  exact fun i hi => h i hi hi

theorem accepted_false (grid : Array Traversal.Cell) (i : Nat) (hi : i < grid.size)
    (h : grid[i].status ≠ 0) : Traversal.accepted grid = false := by
  simp only [Traversal.accepted, Array.all_eq_false, beq_iff_eq]
  exact ⟨i, hi, h⟩

#print axioms accepted_shape
#print axioms acceptedPrefix_complete
#print axioms accepted_false

end Project.EulerRiemann.Execution
