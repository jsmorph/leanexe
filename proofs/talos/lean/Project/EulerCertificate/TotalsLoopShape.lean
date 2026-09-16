import Project.EulerCertificate.TotalsCellExecution
import Project.EulerCertificate.AnnotationMatches

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerRiemann.Traversal (Cell)
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)
open Project.EulerRiemann.Execution (cellValues)

def totalsLoop : Wasm.Program :=
  match (func74[82]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem totals_loop_shape :
    func74[82]? = some (.block 0 0 [.loop 0 0 totalsLoop]) := rfl

structure TotalsScratch where
  cell : Cell := ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩
  previous : Vector := Vectors.zero
  borrowed : UInt64 := 0
  visited : UInt64 := 0

def totalsFrame (owner pointer : UInt64) (count index : Nat)
    (acc : Vector) (scratch : TotalsScratch) : Locals :=
  { params := [.i64 owner, .i64 pointer]
    locals := List.replicate 24 (.i64 0) ++
      (vectorValues acc).reverse ++ (cellValues scratch.cell).reverse ++
      (vectorValues scratch.previous).reverse ++ (cellValues scratch.cell).reverse ++
      (vectorValues acc).reverse ++ (vectorValues acc).reverse ++
      List.replicate 12 (.i64 0) ++
      [.i64 pointer, .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat index),
        .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat count), .i64 scratch.borrowed] ++
      (vectorValues acc).reverse ++ [.i64 scratch.visited] ++ List.replicate 8 (.i64 0)
    values := [] }

def totalsPrefix (grid : Array Cell) (index : Nat) : Vector :=
  Project.ProofKit.ArrayFold.foldPrefix grid Totals.addCell Vectors.zero index

theorem totalsPrefix_zero (grid : Array Cell) :
    totalsPrefix grid 0 = Vectors.zero := by
  simp [totalsPrefix, Project.ProofKit.ArrayFold.foldPrefix]

theorem totalsPrefix_succ (grid : Array Cell) (index : Nat) (hi : index < grid.size) :
    totalsPrefix grid (index + 1) = Totals.addCell (totalsPrefix grid index) grid[index] :=
  Project.ProofKit.ArrayFold.foldPrefix_succ grid Totals.addCell Vectors.zero index hi

theorem totalsPrefix_size (grid : Array Cell) :
    totalsPrefix grid grid.size = Totals.sum grid :=
  Project.ProofKit.ArrayFold.foldPrefix_size grid Totals.addCell Vectors.zero

def totalsInvariant (initial : Store Unit) (owner pointer : UInt64)
    (grid : Array Cell) : AssertionF Unit :=
  fun current frame => current = initial ∧
    ∃ (index : Nat) (scratch : TotalsScratch),
      index ≤ grid.size ∧
      frame = totalsFrame owner pointer grid.size index (totalsPrefix grid index) scratch

def totalsMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 102 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

#print axioms totals_loop_shape
#print axioms totalsPrefix_succ
#print axioms totalsPrefix_size
end Project.EulerCertificate.Execution
