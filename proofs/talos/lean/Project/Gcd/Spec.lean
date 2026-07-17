import Project.Gcd.Program
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Specification for `gcd`
-/

namespace Project.Gcd.Spec

open Wasm

private def gcdFrame
    (a b x y l2 l3 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 : UInt64) :
    Locals :=
  { params := [.i64 a, .i64 b],
    locals := [
      .i64 l2, .i64 l3, .i64 x, .i64 y, .i64 l6, .i64 l7,
      .i64 l8, .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13,
      .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18, .i64 l19],
    values := [] }

private def gcdLoopInv (initial : Store Unit) (a b : UInt64) : AssertionF Unit :=
  fun st s =>
    st = initial ∧
    ∃ l2 l3 x y l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 : UInt64,
      s = gcdFrame a b x y l2 l3 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 ∧
      Nat.gcd x.toNat y.toNat = Nat.gcd a.toNat b.toNat

private def gcdMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals with
  | _ :: _ :: _ :: .i64 y :: _ => y.toNat
  | _ => 0

macro "wp_generated" : tactic =>
  `(tactic|
    (try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure];
     try wp_peel; try simp_all [gcdFrame, gcdMeasure]))

/-- The generated WASM export `gcd` returns the Euclidean greatest common
divisor of two `UInt64` operands. -/
@[spec_of "lean" "LeanExe.Examples.TalosGcd.gcd"]
def GcdSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    TerminatesWith env «module» 0 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

set_option maxHeartbeats 8000000 in
@[proves Project.Gcd.Spec.GcdSpec]
theorem gcd_correct : GcdSpec := by
  intro env initial a b
  apply TerminatesWith.of_wp_entry
    (f := ⟨[.i64, .i64],
      [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64,
       .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64],
      func0, [.i64]⟩) rfl
  intro initial'
  unfold func0
  wp_run
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := gcdLoopInv initial' a b)
    (μ := gcdMeasure)
  · refine ⟨rfl, a, b, a, b, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, rfl⟩
  · rintro st s ⟨rfl, l2, l3, x, y, l6, l7, l8, l9, l10, l11, l12, l13,
      l14, l15, l16, l17, l18, l19, rfl, hgcd⟩
    wp_run
    simp [gcdFrame]
    by_cases hy : y = 0
    · subst hy
      simp [gcdMeasure, Nat.gcd_zero_right] at hgcd ⊢
      wp_generated
      simp [← hgcd, UInt64.ofNat_toNat]
    · have hypos : 0 < y.toNat :=
        Nat.pos_of_ne_zero (by
          intro h
          apply hy
          apply UInt64.toNat.inj
          simpa using h)
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy, gcdMeasure]
      try wp_peel
      try simp [hy, gcdMeasure]
      refine ⟨?_, ?_⟩
      · refine ⟨rfl, l2, l3, y, x % y, x, y, x % y, y, x % y, y, x % y, l13,
          x, y, 0, y, x % y, 1, rfl, ?_⟩
        rw [← hgcd]
        simp [UInt64.toNat_mod]
        rw [Nat.gcd_comm y.toNat (x.toNat % y.toNat), Nat.gcd_comm x.toNat y.toNat]
        exact (Nat.gcd_rec y.toNat x.toNat).symm
      · exact Nat.mod_lt x.toNat hypos

end Project.Gcd.Spec
