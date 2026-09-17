import Project.ExpNeg.Program
import Project.ExpNeg.Model
import Project.ProofKit.BlockLoop
import Project.ProofKit.FixedFrame

namespace Project.ExpNeg.Spec
open Wasm Project.ProofKit

def squareBody : Wasm.Program :=
  [.localGet 0, .constI64 0, .eqI64, .eqz,
   .iff 0 1 [.localGet 3, .constI64 0, .eqI64] [.const 0] [] [.i32],
   .eqz, .br_if 1,
   .localGet 1, .f64ReinterpretI64, .localGet 1, .f64ReinterpretI64,
   .f64Mul, .i64ReinterpretF64, .localSet 4, .localGet 4, .localSet 5,
   .localGet 5, .localSet 1, .localGet 0, .constI64 1, .subI64, .localSet 0, .br 0]

def squareFinish : Wasm.Program :=
  [.localGet 3, .constI64 0, .eqI64,
   .iff 0 0 [.localGet 1, .localSet 2] [], .localGet 2]

theorem square_shape : func2 =
    [.constI64 0, .localSet 3, .block 0 0 [.loop 0 0 squareBody]] ++ squareFinish := rfl

def squareFrame (steps : Nat) (word result a b : UInt64) : Locals :=
  { params := [.i64 (UInt64.ofNat steps), .i64 word]
    locals := [.i64 result, .i64 0, .i64 a, .i64 b]
    values := [] }

def squareInv (initial : Store Unit) (target : UInt64) : AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ steps word result a b,
    steps < 2^64 ∧ frame = squareFrame steps word result a b ∧ square steps word = target

def squareDone (initial : Store Unit) (target : UInt64) : AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ result a b, frame = squareFrame 0 target result a b

def squareMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 0 with | some (.i64 n) => n.toNat | _ => 0

theorem square_step (env : HostEnv Unit) (initial st : Store Unit) (target : UInt64)
    (frame : Locals) (hi : squareInv initial target st frame) :
    wp Project.ExpNeg.module squareBody
      (BlockLoop.stepPost (squareInv initial target) (squareDone initial target)
        squareMeasure (squareMeasure st frame)) st frame env := by
  rcases hi with ⟨hs, steps, word, result, a, b, hn, rfl, ht⟩
  subst st
  cases steps with
  | zero =>
    simp only [square] at ht
    subst target
    wp_fixed_frame [squareBody, squareFrame, BlockLoop.stepPost]
    refine wp_iff_cons rfl ?_
    simp
    wp_fixed_frame [squareFrame, BlockLoop.stepPost]
    exact ⟨rfl, result, a, b, rfl⟩
  | succ steps =>
    have hnword : (UInt64.ofNat (steps+1)).toNat = steps+1 := UInt64.toNat_ofNat_of_lt' hn
    have hnzero : (UInt64.ofNat (steps+1)) ≠ 0 := by
      intro h
      have hh := congrArg UInt64.toNat h
      rw [hnword] at hh
      change steps+1 = 0 at hh
      omega
    wp_fixed_frame [squareBody, squareFrame, BlockLoop.stepPost, hnzero]
    refine wp_iff_cons rfl ?_
    simp
    wp_fixed_frame [squareFrame, BlockLoop.stepPost]
    constructor
    · refine ⟨rfl, steps, Wasm.IEEE64.mul word word, result,
        Wasm.IEEE64.mul word word, Wasm.IEEE64.mul word word, by omega, ?_, ht⟩
      simp [squareFrame, Wasm.f64Mul]
    · change (UInt64.ofNat steps).toNat < (UInt64.ofNat steps+1).toNat
      simp only [UInt64.ofNat_add, UInt64.ofNat_one] at hnword
      rw [hnword, UInt64.toNat_ofNat_of_lt' (by omega : steps < 2^64)]
      omega

theorem square_exact (env : HostEnv Unit) (initial : Store Unit) (steps : Nat)
    (word : UInt64) (hn : steps < 2^64) :
    TerminatesWith env Project.ExpNeg.module 2 initial [.i64 word, .i64 (UInt64.ofNat steps)]
      (fun final values => final = initial ∧ values = [.i64 (square steps word)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.ExpNeg.module func2 _ initial (func2Def.toLocals [.i64 (UInt64.ofNat steps), .i64 word]) env
  rw [square_shape]
  simp only [List.cons_append, List.nil_append]
  wp_fixed_frame [func2Def, List.append]
  refine BlockLoop.program_spec Project.ExpNeg.module env initial _ squareBody
    (squareInv initial (square steps word)) (squareDone initial (square steps word))
    squareMeasure ?_ ?_ ?_ (square_step env initial · (square steps word) · ·) _ squareFinish ?_
  · rintro st frame ⟨_, steps, word, result, a, b, _, rfl, _⟩
    rfl
  · rintro st frame ⟨_, result, a, b, rfl⟩
    rfl
  · exact ⟨rfl, steps, word, 0, 0, 0, hn, rfl, rfl⟩
  · rintro st frame ⟨hs, result, a, b, rfl⟩
    subst st
    wp_fixed_frame [squareFinish, squareFrame]
    refine wp_iff_cons rfl ?_
    simp

#print axioms square_exact
end Project.ExpNeg.Spec
