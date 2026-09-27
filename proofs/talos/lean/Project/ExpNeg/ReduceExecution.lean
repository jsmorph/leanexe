import Project.ExpNeg.Program
import Project.ExpNeg.Model
import Project.ProofKit.BlockLoop
import Project.ProofKit.FixedFrame

namespace Project.ExpNeg.Spec
open Wasm Project.ProofKit

def reduceBody : Wasm.Program :=
  [
    .localGet 0,
    .constI64 0,
    .eqI64,
    .eqz,
    .iff 0 1 [
     .localGet 5,
     .constI64 0,
     .eqI64
    ] [
     .const 0
    ] [] [.i32],
    .eqz,
    .br_if 1,
    .localGet 1,
    .constI64 13830554455654793216,
    .leUI64,
    .iff 0 0 [
     .localGet 1,
     .localSet 3,
     .localGet 2,
     .localSet 4,
     .constI64 1,
     .localSet 5
    ] [
     .localGet 1,
     .f64ReinterpretI64,
     .constI64 4602678819172646912,
     .f64ReinterpretI64,
     .f64Mul,
     .i64ReinterpretF64,
     .localSet 6,
     .localGet 6,
     .localSet 7,
     .localGet 2,
     .localSet 11,
     .constI64 1,
     .localSet 12,
     .localGet 11,
     .localGet 12,
     .addI64,
     .localTee 13,
     .localGet 11,
     .ltUI64,
     .iff 0 1 [
      .unreachable
     ] [
      .localGet 13
     ] [] [.i64],
     .localSet 8,
     .localGet 7,
     .localSet 9,
     .localGet 8,
     .localSet 10,
     .localGet 9,
     .localSet 1,
     .localGet 10,
     .localSet 2,
     .localGet 0,
     .constI64 1,
     .subI64,
     .localSet 0
    ],
    .br 0
  ]

def reduceFinish : Wasm.Program :=
  [.localGet 5, .constI64 0, .eqI64,
   .iff 0 0 [.localGet 1, .localSet 3, .localGet 2, .localSet 4] [],
   .localGet 3, .localGet 4]

theorem reduce_shape : func1 =
    [.constI64 0, .localSet 5, .block 0 0 [.loop 0 0 reduceBody]] ++ reduceFinish := rfl

def reduceFrame (steps : Nat) (word : UInt64) (squares : Nat) (result : Reduction)
    (done : Bool) (t : Fin 8 → UInt64) : Locals :=
  { params := [.i64 (UInt64.ofNat steps), .i64 word, .i64 (UInt64.ofNat squares)]
    locals := [.i64 result.word, .i64 (UInt64.ofNat result.squares), .i64 (if done then 1 else 0),
      .i64 (t 0), .i64 (t 1), .i64 (t 2), .i64 (t 3), .i64 (t 4), .i64 (t 5), .i64 (t 6), .i64 (t 7)]
    values := [] }

def reduceInv (initial : Store Unit) (target : Reduction) : AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ steps word squares result done t,
    steps+squares < 2^64 ∧ result.squares < 2^64 ∧
    frame = reduceFrame steps word squares result done t ∧
    (if done then result else reduce steps word squares) = target

def reduceDone (initial : Store Unit) (target : Reduction) : AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ steps word squares result done t,
    frame = reduceFrame steps word squares result done t ∧
    (if done then result else ⟨word, squares⟩) = target

def reduceMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 0, frame.get 5 with
  | some (.i64 n), some (.i64 flag) => if flag = 0 then n.toNat+1 else 0
  | _, _ => 0

syntax "wp_reduce" (Lean.Parser.Tactic.simpArgs)? : tactic
macro_rules
  | `(tactic| wp_reduce $[[$args,*]]?) => do
    let extra := args.map (·.getElems) |>.getD #[]
    `(tactic| repeat first
      | wp_fixed_frame [reduceBody, reduceFrame, BlockLoop.stepPost, Wasm.f64Mul, $extra,*]
      | (refine wp_iff_cons rfl ?_; simp [$extra,*]))

theorem reduce_step (env : HostEnv Unit) (initial st : Store Unit) (target : Reduction)
    (frame : Locals) (hi : reduceInv initial target st frame) :
    wp Project.ExpNeg.module reduceBody
      (BlockLoop.stepPost (reduceInv initial target) (reduceDone initial target)
        reduceMeasure (reduceMeasure st frame)) st frame env := by
  rcases hi with ⟨hs, steps, word, squares, result, done, t, hn, hr, rfl, ht⟩
  subst st
  cases done with
  | true =>
    simp only [ite_true] at ht
    by_cases hz : UInt64.ofNat steps = 0
    all_goals
      wp_reduce [hz]
      refine ⟨rfl, steps, word, squares, result, true, t, ?_, ht⟩
      simp [reduceFrame, hz]
  | false =>
    simp only [Bool.false_eq_true, ite_false] at ht
    cases steps with
    | zero =>
      wp_reduce
      exact ⟨rfl, 0, word, squares, result, false, t, rfl, ht⟩
    | succ steps =>
      have hstepNat : (UInt64.ofNat (steps+1)).toNat = steps+1 :=
        UInt64.toNat_ofNat_of_lt' (by change steps+1 < 2^64; omega)
      have hz : UInt64.ofNat (steps+1) ≠ 0 := by
        intro he
        have hh := congrArg UInt64.toNat he
        rw [hstepNat] at hh
        change steps+1 = 0 at hh
        omega
      have hk : (UInt64.ofNat squares).toNat = squares :=
        UInt64.toNat_ofNat_of_lt' (by change squares < 2^64; omega)
      have hk1 : (UInt64.ofNat squares+1).toNat = squares+1 := by
        simpa only [UInt64.ofNat_add, UInt64.ofNat_one] using
          UInt64.toNat_ofNat_of_lt' (show squares+1 < 2^64 by omega)
      have hover : ¬UInt64.ofNat squares+1 < UInt64.ofNat squares := by
        rw [UInt64.lt_iff_toNat_lt, hk, hk1]
        omega
      by_cases hx : word ≤ 0xBFF0000000000000
      · wp_reduce [hz, hx]
        constructor
        · exact ⟨rfl, steps+1, word, squares, ⟨word, squares⟩, true, t,
            hn, by change squares < 2^64; omega,
            by simp [reduceFrame, UInt64.ofNat_add], by simpa [reduce, hx] using ht⟩
        · simp [reduceMeasure, Locals.get]
      · wp_reduce [hz, hx, hover]
        constructor
        · let next := Wasm.IEEE64.mul word 0x3FE0000000000000
          let ts : Fin 8 → UInt64 := fun i =>
            [next, next, UInt64.ofNat (squares+1), next, UInt64.ofNat (squares+1),
              UInt64.ofNat squares, 1, UInt64.ofNat (squares+1)][i]!
          refine ⟨rfl, steps, next, squares+1, result, false, ts, by omega, hr, ?_, ?_⟩
          · simp [reduceFrame, ts, next, UInt64.ofNat_add]
          · simpa only [reduce, ite_eq_right hx, Bool.false_eq_true, ite_false] using ht
        · change (UInt64.ofNat steps).toNat+1 < (UInt64.ofNat steps+1).toNat+1
          simp only [UInt64.ofNat_add, UInt64.ofNat_one] at hstepNat
          rw [hstepNat, UInt64.toNat_ofNat_of_lt' (show steps < 2^64 by omega)]
          omega

#print axioms reduce_step

theorem reduce_count_le (steps squares : Nat) (word : UInt64) :
    (reduce steps word squares).squares ≤ squares+steps := by
  induction steps generalizing word squares with
  | zero => simp [reduce]
  | succ steps ih =>
    simp only [reduce]
    split
    · simp
    · exact (ih (squares+1) _).trans (by omega)

theorem reduce_exact (env : HostEnv Unit) (initial : Store Unit) (steps squares : Nat)
    (word : UInt64) (hn : steps+squares < 2^64) :
    TerminatesWith env Project.ExpNeg.module 1 initial
      [.i64 (UInt64.ofNat squares), .i64 word, .i64 (UInt64.ofNat steps)]
      (fun final values => final = initial ∧
        values = [.i64 (UInt64.ofNat (reduce steps word squares).squares),
          .i64 (reduce steps word squares).word]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.ExpNeg.module func1 _ initial
    (func1Def.toLocals [.i64 (UInt64.ofNat steps), .i64 word, .i64 (UInt64.ofNat squares)]) env
  rw [reduce_shape]
  simp only [List.cons_append, List.nil_append]
  wp_fixed_frame [func1Def]
  refine BlockLoop.program_spec Project.ExpNeg.module env initial _ reduceBody
    (reduceInv initial (reduce steps word squares)) (reduceDone initial (reduce steps word squares))
    reduceMeasure ?_ ?_ ?_ (reduce_step env initial · (reduce steps word squares) · ·) _ reduceFinish ?_
  · rintro st frame ⟨_, steps, word, squares, result, done, t, _, _, rfl, _⟩
    rfl
  · rintro st frame ⟨_, steps, word, squares, result, done, t, rfl, _⟩
    rfl
  · exact ⟨rfl, steps, word, squares, ⟨0, 0⟩, false, fun _ => 0, hn,
      by change 0 < 2^64; norm_num, rfl, rfl⟩
  · rintro st frame ⟨hs, n, x, k, result, done, t, rfl, ht⟩
    subst st
    cases done <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ht
    all_goals
      unfold reduceFinish
      wp_reduce [← ht]

#print axioms reduce_exact

end Project.ExpNeg.Spec
