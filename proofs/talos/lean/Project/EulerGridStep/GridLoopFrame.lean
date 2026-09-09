import Project.EulerGridStep.GridLoopShape

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- All scratch slots, including entry values that the outer loop preserves. -/
structure GridScratch where
  l2 : UInt64 := 0
  l3 : UInt64 := 0
  l5 : UInt64 := 0
  l6 : UInt64 := 0
  l8 : UInt64 := 0
  l9 : UInt64 := 0
  l13 : UInt64 := 0
  l14 : UInt64 := 0
  l15 : UInt64 := 0
  l16 : UInt64 := 0
  l17 : UInt64 := 0
  l18 : UInt64 := 0
  l19 : UInt64 := 0
  l20 : UInt64 := 0
  l21 : UInt64 := 0
  l22 : UInt64 := 0
  l23 : UInt64 := 0
  l24 : UInt64 := 0
  l25 : UInt64 := 0
  l26 : UInt64 := 0
  l27 : UInt64 := 0
  l28 : UInt64 := 0
  l29 : UInt64 := 0
  l30 : UInt64 := 0
  l31 : UInt64 := 0
  l32 : UInt64 := 0
  l33 : UInt64 := 0
  l34 : UInt64 := 0
  l35 : UInt64 := 0
  l36 : UInt64 := 0
  l37 : UInt64 := 0
  l38 : UInt64 := 0
  l39 : UInt64 := 0
  l40 : UInt64 := 0
  l41 : UInt64 := 0
  l42 : UInt64 := 0
  l43 : UInt64 := 0
  l44 : UInt64 := 0
  deriving Inhabited

def gridLoopFrame (ratio pointer initialRoot currentRoot : UInt64) (count index : Nat)
    (scratch : GridScratch) : Locals :=
  { params := [.i64 ratio, .i64 pointer]
    locals := [
      .i64 scratch.l2,
      .i64 scratch.l3,
      .i64 (UInt64.ofNat count),
      .i64 scratch.l5,
      .i64 scratch.l6,
      .i64 initialRoot,
      .i64 scratch.l8,
      .i64 scratch.l9,
      .i64 currentRoot,
      .i64 currentRoot,
      .i64 (UInt64.ofNat index),
      .i64 scratch.l13,
      .i64 scratch.l14,
      .i64 scratch.l15,
      .i64 scratch.l16,
      .i64 scratch.l17,
      .i64 scratch.l18,
      .i64 scratch.l19,
      .i64 scratch.l20,
      .i64 scratch.l21,
      .i64 scratch.l22,
      .i64 scratch.l23,
      .i64 scratch.l24,
      .i64 scratch.l25,
      .i64 scratch.l26,
      .i64 scratch.l27,
      .i64 scratch.l28,
      .i64 scratch.l29,
      .i64 scratch.l30,
      .i64 scratch.l31,
      .i64 scratch.l32,
      .i64 scratch.l33,
      .i64 scratch.l34,
      .i64 scratch.l35,
      .i64 scratch.l36,
      .i64 scratch.l37,
      .i64 scratch.l38,
      .i64 scratch.l39,
      .i64 scratch.l40,
      .i64 scratch.l41,
      .i64 scratch.l42,
      .i64 scratch.l43,
      .i64 scratch.l44]
    values := [] }

def gridLoopInvariant (ratio pointer : UInt64) (input : Array UInt64) (base : Nat)
    (target : Array UInt64) : AssertionF Unit :=
  fun current frame => UInt64Array.At current pointer input ∧
    ∃ (index : Nat) (output : Array UInt64) (a r f : UInt64) (scratch : GridScratch),
      index ≤ input.size / 3 ∧ output.size = 1 + 6 * (input.size / 3) ∧
      GridLoopStorage current base (input.size / 3) index output a r f ∧
      (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At current output.size ∧
      target = gridRemaining ratio input (input.size / 3) index output ∧
      frame = gridLoopFrame ratio pointer (arenaRoot base output.size 0)
        (gridLoopRoot base output.size index output[0]!) (input.size / 3) index scratch

def gridLoopMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 12 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

theorem gridLoopMeasure_frame (count index : Nat) (initial : Store Unit)
    (ratio pointer initialRoot currentRoot : UInt64) (scratch : GridScratch) (hi : index < UInt64.size) :
    gridLoopMeasure count initial (gridLoopFrame ratio pointer initialRoot currentRoot count index scratch) =
      count - index + 1 := by
  simp [gridLoopMeasure, gridLoopFrame, Locals.get, UInt64.toNat_ofNat_of_lt' hi]

def gridSteppedScratch (scratch : GridScratch) (ratio pointer currentRoot nextRoot : UInt64)
    (index : Nat) : GridScratch :=
  { scratch with
    l13 := currentRoot
    l14 := currentRoot
    l15 := UInt64.ofNat index
    l16 := ratio
    l17 := 0
    l18 := pointer
    l19 := currentRoot
    l20 := currentRoot
    l21 := UInt64.ofNat index
    l22 := nextRoot
    l23 := nextRoot
    l24 := nextRoot
    l25 := nextRoot
    l26 := UInt64.ofNat (index + 1)
    l27 := nextRoot
    l28 := nextRoot
    l29 := UInt64.ofNat (index + 1)
    l33 := currentRoot
    l34 := 0
    l35 := UInt64.ofNat (index + 1)
    l36 := 0
    l37 := nextRoot
    l38 := nextRoot
    l39 := UInt64.ofNat (index + 1)
    l40 := 1 }

def gridDoneScratch (scratch : GridScratch) (currentRoot : UInt64) (count index : Nat) : GridScratch :=
  { scratch with
    l13 := currentRoot
    l14 := currentRoot
    l15 := UInt64.ofNat index
    l27 := currentRoot
    l28 := currentRoot
    l29 := UInt64.ofNat index
    l33 := if index < count then currentRoot else scratch.l33
    l34 := if index < count then 0 else scratch.l34
    l36 := 1
    l37 := currentRoot
    l38 := currentRoot
    l39 := UInt64.ofNat index
    l40 := 1 }

#print axioms gridLoopMeasure_frame
end Project.EulerGridStep.Execution
