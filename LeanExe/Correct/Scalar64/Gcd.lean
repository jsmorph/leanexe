import LeanExe.Correct.Scalar64.Arithmetic
import LeanExe.Correct.Scalar64.Iteration
import LeanExe.Examples.TalosGcd

namespace LeanExe.Correct.Scalar64
open LeanExe.TypeSafety

theorem remainder_decreases (a b : UInt64) (nonzero : b ≠ 0) :
    (a % b).toNat < b.toNat := by
  rw [UInt64.toNat_mod]
  apply Nat.mod_lt
  have : b.toNat ≠ 0 := by
    intro eq
    apply nonzero
    apply UInt64.toNat_inj.mp
    exact eq
  omega

/-- A total mathematical account of the carried pair; it is not a source replacement. -/
def gcdResult (a b : UInt64) : MProd UInt64 UInt64 :=
  if _h : b = 0 then ⟨a, b⟩ else gcdResult b (a % b)
termination_by b.toNat
decreasing_by apply remainder_decreases; assumption

def gcdStep (state : MProd UInt64 UInt64) : Sum (MProd UInt64 UInt64) (MProd UInt64 UInt64) :=
  forInStep (if @bne UInt64 instBEqOfDecidableEq state.2 0 then
    ForInStep.yield ⟨state.2, state.1 % state.2⟩ else ForInStep.done ⟨state.1, state.2⟩)

theorem gcd_iterates (a b : UInt64) :
    Iterates gcdStep ⟨a, b⟩ (gcdResult a b) := by
  rw [gcdResult.eq_def]
  split
  next h => exact .done (by simp [gcdStep, forInStep, h])
  next h =>
    exact .next (by simp [gcdStep, forInStep, h]) (gcd_iterates b (a % b))
termination_by b.toNat
decreasing_by apply remainder_decreases; assumption

theorem gcd_fixed :
    repeatM.body (m := Id) gcdStep (fun state => gcdResult state.1 state.2) =
      (fun state => gcdResult state.1 state.2) := by
  funext ⟨a, b⟩
  conv => rhs; rw [gcdResult.eq_def]
  by_cases h : b = 0 <;> simp [repeatM.body, gcdStep, forInStep, h, Bind.bind, Pure.pure]

theorem gcd_original (a b : UInt64) :
    LeanExe.Examples.TalosGcd.gcd a b = (gcdResult a b).1 := by
  have same := (gcd_iterates a b).repeatM_eq ⟨_, gcd_fixed⟩
  unfold LeanExe.Examples.TalosGcd.gcd
  simp only [ForIn.forIn, loop_forIn_eq, Bind.bind, Pure.pure, Id.run]
  erw [same]

theorem Runs.rem (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .mod left right) env (encodeWord (a % b)) := by
  simpa [encodeWord, evalWordBin, WordWidth.modulus, WordWidth.bits,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.toNat_lt)] using
    Runs.bin (op := .mod) leftRun rightRun

def gcdBody : Expr :=
  .ifE (.wordCmp .w64 .eq (.var 1) (.word .w64 0)) (.var 0)
    (.call 0 [.var 1, .wordBin .w64 .mod (.var 0) (.var 1)])

theorem gcd_core (a b : UInt64) :
    Runs [gcdBody] gcdBody (encodeArgs [a, b]) (encodeWord (gcdResult a b).1) := by
  conv => rhs; rw [gcdResult.eq_def]
  have condition : Runs [gcdBody] (.wordCmp .w64 .eq (.var 1) (.word .w64 0))
      (encodeArgs [a, b]) (.bool (b == 0)) := Runs.eq (Runs.var rfl) Runs.word
  split
  next h =>
    exact Runs.ifTrue (by simpa [h] using condition) (Runs.var rfl)
  next h =>
    have hb : (b == 0) = false := Bool.eq_false_iff.mpr (fun eq => h (beq_iff_eq.mp eq))
    apply Runs.ifFalse (by simpa only [hb] using condition)
    exact Runs.call2 rfl (Runs.var rfl) (Runs.rem (Runs.var rfl) (Runs.var rfl))
      (gcd_core b (a % b))
termination_by b.toNat
decreasing_by apply remainder_decreases; assumption

def gcdCertificate : SourceCertificate (UInt64 × UInt64)
    (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.TalosGcd.gcd input.1 input.2)
    [gcdBody] [binarySignature] 0 where
  body := gcdBody
  arity := 2
  admitted := by decide
  bodyAt := rfl
  signatureAt := rfl
  argsLength := fun _ => rfl
  computes := fun input => by
    rw [gcd_original]
    exact gcd_core input.1 input.2

end LeanExe.Correct.Scalar64
