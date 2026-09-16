import Project.EulerCertificate.BoundaryFaceExecution
import Project.EulerCertificate.AnnotationMatches
import Project.EulerRiemann.TraversalSweep

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerRiemann.Traversal (Cell)
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)
open Project.EulerRiemann.Execution (cellValues boolWord)

def boundaryLoop : Wasm.Program :=
  match (func173[78]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem boundary_loop_shape :
    func173[78]? = some (.block 0 0 [.loop 0 0 boundaryLoop]) := rfl

structure BoundaryScratch where
  cell : Cell := ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩
  previous : Vector := Vectors.zero
  flux : Vector := Vectors.zero
  copied : Bool := false

def boundaryFrame (n : Nat) (trials : UInt64) (axis : Bool)
    (owner pointer : UInt64) (count index : Nat) (acc : Vector)
    (scratch : BoundaryScratch) : Locals :=
  { params := [.i64 (UInt64.ofNat n), .i64 trials, .i64 (boolWord axis), .i64 owner, .i64 pointer]
    locals := List.replicate 24 (.i64 0) ++
      (vectorValues acc).reverse ++ (cellValues scratch.cell).reverse ++
      [.i64 (if scratch.copied then UInt64.ofNat n else 0),
        .i64 (if scratch.copied then trials else 0),
        .i64 (if scratch.copied then boolWord axis else 0),
        .i64 (if scratch.copied then owner else 0),
        .i64 (if scratch.copied then pointer else 0), .i64 (UInt64.ofNat scratch.cell.index)] ++
      (vectorValues scratch.flux).reverse ++ (vectorValues scratch.flux).reverse ++
      (vectorValues scratch.previous).reverse ++ (vectorValues scratch.flux).reverse ++
      (vectorValues acc).reverse ++ (vectorValues acc).reverse ++ List.replicate 12 (.i64 0) ++
      [.i64 pointer, .i64 (UInt64.ofNat count), .i64 (UInt64.ofNat index),
        .i64 (UInt64.ofNat n), .i64 (UInt64.ofNat n), .i64 0] ++
      (vectorValues acc).reverse ++ [.i64 (boolWord scratch.copied)] ++ List.replicate 7 (.i64 0)
    values := [] }

def boundaryPrefix (n trials : Nat) (axis : Bool) (grid : Array Cell) (index : Nat) : Vector :=
  Project.ProofKit.ArrayFold.foldPrefix grid
    (fun acc cell => Vectors.add acc (Boundary.line n trials axis grid cell.index)) Vectors.zero index

theorem boundaryPrefix_zero (n trials : Nat) (axis : Bool) (grid : Array Cell) :
    boundaryPrefix n trials axis grid 0 = Vectors.zero := by
  simp [boundaryPrefix, Project.ProofKit.ArrayFold.foldPrefix]

theorem boundaryPrefix_succ (n trials : Nat) (axis : Bool) (grid : Array Cell)
    (index : Nat) (hi : index < grid.size) :
    boundaryPrefix n trials axis grid (index + 1) =
      Vectors.add (boundaryPrefix n trials axis grid index)
        (Boundary.line n trials axis grid grid[index].index) :=
  Project.ProofKit.ArrayFold.foldPrefix_succ grid _ Vectors.zero index hi

theorem boundaryPrefix_complete (n trials : Nat) (axis : Bool) (grid : Array Cell) :
    boundaryPrefix n trials axis grid n = Boundary.sum n trials axis grid :=
  Array.foldl_eq_foldl_extract.symm

def boundaryInvariant (initial : Store Unit) (n : Nat) (trials : UInt64) (axis : Bool)
    (owner pointer : UInt64) (grid : Array Cell) : AssertionF Unit :=
  fun current frame => current = initial ∧
    ∃ (index : Nat) (scratch : BoundaryScratch), index ≤ n ∧
      frame = boundaryFrame n trials axis owner pointer grid.size index
        (boundaryPrefix n trials.toNat axis grid index) scratch

def boundaryMeasure (n : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 140 with
  | some (.i64 index) => n - index.toNat + 1
  | _ => 0

#print axioms boundary_loop_shape
#print axioms boundaryPrefix_succ
#print axioms boundaryPrefix_complete
end Project.EulerCertificate.Execution
