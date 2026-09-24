import Project.Correct.Scalar64.Certificate
import LeanExe.Correct.Scalar64.Gcd

namespace Project.Correct.Scalar64.Pilots
open Wasm
open Project.ProofKit.ScalarTransition

def gcdBody : Command :=
  .seq (.assign 2 (.bin .remU (.get 0) (.get 1)))
    (.seq (.assign 0 (.get 1)) (.assign 1 (.get 2)))

def gcd : Function :=
  { arity := 2, localCount := 3, scratch := 3
    body := .loop (.ne (.get 1) (.const 0)) gcdBody
    result := .get 0 }

def gcdState (a b r s t : UInt64) : State :=
  { params := [.i64 a, .i64 b], locals := [.i64 r, .i64 s, .i64 t] }

theorem gcdBody_exec (a b r s t : UInt64) :
    Executes functions 3 gcdBody (gcdState a b r s t) (gcdState b (a % b) (a % b) a b) := by
  apply Executes.seq (middle := gcdState a b (a % b) a b)
  · apply Executes.assign (value := a % b) (afterValue := gcdState a b r a b)
    · by_cases h : b = 0 <;>
        simp [Expr.eval, State.get, State.set?, gcdState, U64Op.apply, h]
    · rfl
  · apply Executes.seq (middle := gcdState b b (a % b) a b)
    · exact Executes.assign rfl rfl
    · exact Executes.assign rfl rfl

/-- Final IR frame, including staging/scratch words, with a proved decreasing
measure. This is a proof-level definition; the emitted program uses a WASM loop. -/
def gcdFinal (a b r s t : UInt64) : State :=
  if _h : b = 0 then gcdState a b r s t else gcdFinal b (a % b) (a % b) a b
termination_by b.toNat
decreasing_by apply LeanExe.Correct.Scalar64.remainder_decreases; assumption

theorem gcdFinal_get (a b r s t : UInt64) :
    (gcdFinal a b r s t).get 0 =
      some (.i64 (LeanExe.Correct.Scalar64.gcdResult a b).1) := by
  rw [gcdFinal.eq_def, LeanExe.Correct.Scalar64.gcdResult.eq_def]
  by_cases h : b = 0
  · simp [h, gcdState, State.get]
  · simpa [h] using gcdFinal_get b (a % b) (a % b) a b
termination_by b.toNat
decreasing_by apply LeanExe.Correct.Scalar64.remainder_decreases; assumption

/-- Selectors used only in the loop invariant; its shape premise establishes
that these slots exist and contain i64 values. Runtime reads remain checked. -/
def wordAt (state : State) (index : Nat) : UInt64 :=
  match state.get index with
  | some (.i64 value) => value
  | _ => 0

def gcdAdvance (state : State) : State :=
  gcdState (wordAt state 1) (wordAt state 0 % wordAt state 1)
    (wordAt state 0 % wordAt state 1) (wordAt state 0) (wordAt state 1)

theorem gcd_exec (a b : UInt64) :
    Executes [gcd] gcd.scratch gcd.body (gcd.initial [a, b]) (gcdFinal a b 0 0 0) := by
  let expected := gcdFinal a b 0 0 0
  let Inv : State → Prop := fun current => ∃ x y r s t,
    current = gcdState x y r s t ∧ gcdFinal x y r s t = expected
  apply Executes.loop Inv (fun current => (wordAt current 1).toNat)
    (fun current => wordAt current 1 != 0) id gcdAdvance
  · exact ⟨a, b, 0, 0, 0, rfl, rfl⟩
  · intro current currentInv
    rcases currentInv with ⟨x, y, r, s, t, rfl, finalEq⟩
    simp [gcd, Expr.eval, wordAt, gcdState, State.get]
  · intro current currentInv continuing
    rcases currentInv with ⟨x, y, r, s, t, rfl, finalEq⟩
    simpa [gcd, gcdAdvance, wordAt, gcdState, State.get] using
      (gcdBody_exec (functions := [gcd]) x y r s t)
  · intro current currentInv continuing
    rcases currentInv with ⟨x, y, r, s, t, rfl, finalEq⟩
    have nonzero : y ≠ 0 := by simpa [wordAt, gcdState, State.get] using continuing
    refine ⟨y, x % y, x % y, x, y, ?_, ?_⟩
    · simp [gcdAdvance, wordAt, gcdState, State.get]
    · rw [gcdFinal.eq_def] at finalEq
      simpa [nonzero] using finalEq
  · intro current currentInv continuing
    rcases currentInv with ⟨x, y, r, s, t, rfl, finalEq⟩
    have nonzero : y ≠ 0 := by simpa [wordAt, gcdState, State.get] using continuing
    simpa [gcdAdvance, wordAt, gcdState, State.get] using
      LeanExe.Correct.Scalar64.remainder_decreases x y nonzero
  · intro current currentInv exiting
    rcases currentInv with ⟨x, y, r, s, t, rfl, finalEq⟩
    have zero : y = 0 := by simpa [wordAt, gcdState, State.get] using exiting
    rw [gcdFinal.eq_def] at finalEq
    simpa [zero] using finalEq

def gcdCertificate : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.TalosGcd.gcd input.1 input.2) where
  core := [LeanExe.Correct.Scalar64.gcdBody]
  signatures := [LeanExe.Correct.Scalar64.binarySignature]
  coreEntry := 0
  sourceProof := LeanExe.Correct.Scalar64.gcdCertificate
  functions := [gcd]
  entry := 0
  exportName := "gcd"
  function := gcd
  found := rfl
  arity := rfl
  admitted := by decide
  lowering := fun (a, b) => ⟨gcdFinal a b 0 0 0, gcdFinal a b 0 0 0, gcd_exec a b, by
    simp only [gcd, Expr.eval, gcdFinal_get, LeanExe.Correct.Scalar64.gcd_original]
    rfl⟩

end Project.Correct.Scalar64.Pilots
