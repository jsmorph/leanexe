import Project.EulerGridScan.LoopShape

namespace Project.EulerGridScan.Execution
open Wasm

/-- Scratch slots written by the generated loop; local 27 is preserved separately. -/
structure Scratch where
  l8 : UInt64 := 0
  l9 : UInt64 := 0
  l10 : UInt64 := 0
  l11 : UInt64 := 0
  l12 : UInt64 := 0
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
  deriving Inhabited

def loopFrame (pointer : UInt64) (count index : Nat) (status speed preserved27 : UInt64)
    (scratch : Scratch) : Locals :=
  { params := [.i64 pointer],
    locals := [
      .i64 (UInt64.ofNat count),
      .i64 0,
      .i64 0,
      .i64 0,
      .i64 (UInt64.ofNat index),
      .i64 status,
      .i64 speed,
      .i64 scratch.l8,
      .i64 scratch.l9,
      .i64 scratch.l10,
      .i64 scratch.l11,
      .i64 scratch.l12,
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
      .i64 preserved27,
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
      .i64 scratch.l40],
    values := [] }

def loopInvariant (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (count : Nat) (preserved27 : UInt64) (target : Project.EulerGridStep.Model.CheckedSpeed) : AssertionF Unit :=
  fun current frame => current = initial ∧
    ∃ (index : Nat) (status speed : UInt64) (scratch : Scratch),
      index ≤ count ∧ target = remaining input count index status speed ∧
      frame = loopFrame pointer count index status speed preserved27 scratch

def loopMeasure (count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 5 with
  | some (.i64 index) => count - index.toNat + 1
  | _ => 0

theorem loopMeasure_frame (count index : Nat) (initial : Store Unit)
    (pointer status speed preserved27 : UInt64) (scratch : Scratch) (hi : index < UInt64.size) :
    loopMeasure count initial (loopFrame pointer count index status speed preserved27 scratch) =
      count - index + 1 := by
  simp [loopMeasure, loopFrame, Locals.get, UInt64.toNat_ofNat_of_lt' hi]


def steppedScratch (scratch : Scratch) (pointer : UInt64) (index : Nat)
    (status speed nextStatus nextSpeed : UInt64) : Scratch :=
  { scratch with
    l8 := UInt64.ofNat index
    l9 := status
    l10 := speed
    l11 := status
    l12 := speed
    l13 := 0
    l14 := pointer
    l15 := UInt64.ofNat index
    l16 := speed
    l17 := nextStatus
    l18 := nextSpeed
    l19 := nextStatus
    l20 := nextSpeed
    l21 := nextStatus
    l22 := nextSpeed
    l23 := UInt64.ofNat (index + 1)
    l24 := UInt64.ofNat (index + 1)
    l25 := nextStatus
    l26 := nextSpeed
    l33 := UInt64.ofNat index
    l34 := 1
    l35 := UInt64.ofNat (index + 1)
    l36 := 0
    l37 := UInt64.ofNat (index + 1)
    l38 := nextStatus
    l39 := nextSpeed
    l40 := 1 }

def doneScratch (scratch : Scratch) (index : Nat) (status speed : UInt64) : Scratch :=
  { scratch with
    l8 := UInt64.ofNat index
    l9 := status
    l10 := speed
    l11 := status
    l12 := speed
    l24 := UInt64.ofNat index
    l25 := status
    l26 := speed
    l36 := 1
    l37 := UInt64.ofNat index
    l38 := status
    l39 := speed
    l40 := 1 }

end Project.EulerGridScan.Execution
