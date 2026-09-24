import LeanExe.Correct.Scalar64.Profile
import LeanExe.TypeSafety.Continuations

/-!
# Source certificates and compositional core execution

Certificates mention the original Lean function. Their proposition is execution
of the independent TypeSafety machine, not an equality with a compiler evaluator.
The input type is a proof-level grouping of scalar ABI arguments.
-/

namespace LeanExe.Correct.Scalar64

open LeanExe.TypeSafety

def encodeWord (value : UInt64) : Value := .word .w64 value.toNat
def encodeArgs (args : List UInt64) : Env := args.map encodeWord

def Runs (program : Program) (expr : Expr) (env : Env) (value : Value) : Prop :=
  Steps program (.eval expr env []) (.ret value [])

theorem Runs.withKont (h : Runs program expr env value) (kont : Kont) :
    Steps program (.eval expr env kont) (.ret value kont) := by
  simpa [State.appendKont] using h.appendKont kont

theorem Runs.word : Runs program (.word .w64 value) env (.word .w64 value) :=
  .tail .refl rfl

theorem Runs.bool : Runs program (.bool value) env (.bool value) :=
  .tail .refl rfl

theorem Runs.var (found : lookup env index = some value) :
    Runs program (.var index) env value := by
  exact .tail .refl (by simp [Step, step, found])

theorem prepend (execution : Steps program middle last)
    (transition : Step program first middle) : Steps program first last :=
  (Steps.tail .refl transition).trans execution

theorem Runs.letE (bound : Runs program value env v)
    (bodyRun : Runs program body (v :: env) result) :
    Runs program (.letE value body) env result := by
  exact prepend ((bound.withKont [.letBody body env]).trans (prepend bodyRun rfl)) rfl

theorem Runs.ifTrue (condition : Runs program conditionExpr env (.bool true))
    (branch : Runs program yes env result) :
    Runs program (.ifE conditionExpr yes no) env result := by
  exact prepend ((condition.withKont [.ifBranches yes no env]).trans
    (prepend branch rfl)) rfl

theorem Runs.ifFalse (condition : Runs program conditionExpr env (.bool false))
    (branch : Runs program no env result) :
    Runs program (.ifE conditionExpr yes no) env result := by
  exact prepend ((condition.withKont [.ifBranches yes no env]).trans
    (prepend branch rfl)) rfl

theorem Runs.bin (leftRun : Runs program left env (.word .w64 a))
    (rightRun : Runs program right env (.word .w64 b)) :
    Runs program (.wordBin .w64 op left right) env
      (.word .w64 (evalWordBin .w64 op a b)) := by
  have finish : Steps program
      (.ret (.word .w64 b) [.wordBinRight .w64 op (.word .w64 a)])
      (.ret (.word .w64 (evalWordBin .w64 op a b)) []) := .tail .refl rfl
  exact prepend ((leftRun.withKont [.wordBinLeft .w64 op right env]).trans
    (prepend ((rightRun.withKont [.wordBinRight .w64 op (.word .w64 a)]).trans finish) rfl)) rfl

theorem Runs.cmp (leftRun : Runs program left env (.word .w64 a))
    (rightRun : Runs program right env (.word .w64 b)) :
    Runs program (.wordCmp .w64 op left right) env
      (.bool (NatCmpOp.apply op a b)) := by
  have finish : Steps program
      (.ret (.word .w64 b) [.wordCmpRight .w64 op (.word .w64 a)])
      (.ret (.bool (NatCmpOp.apply op a b)) []) := .tail .refl rfl
  exact prepend ((leftRun.withKont [.wordCmpLeft .w64 op right env]).trans
    (prepend ((rightRun.withKont [.wordCmpRight .w64 op (.word .w64 a)]).trans finish) rfl)) rfl

theorem Runs.call2 (found : lookup program function = some body)
    (leftRun : Runs program left env a) (rightRun : Runs program right env b)
    (bodyRun : Runs program body [a, b] result) :
    Runs program (.call function [left, right]) env result := by
  have finish : Steps program (.ret b [.callArgs function [a] [] env])
      (.ret result []) :=
    prepend bodyRun (by simp [Step, step, enterCall, found])
  exact prepend ((leftRun.withKont [.callArgs function [] [right] env]).trans
    (prepend ((rightRun.withKont [.callArgs function [a] [] env]).trans finish) rfl)) rfl

theorem encodeWord_typed (value : UInt64) : ValueTyped [] (encodeWord value) (.word .w64) :=
  .word value.toNat_lt

theorem encodeArgs_typed (args : List UInt64) :
    EnvTyped [] (encodeArgs args) (List.replicate args.length (.word .w64)) := by
  induction args with
  | nil => exact .nil
  | cons head tail ih => exact .cons (encodeWord_typed head) ih

/-- Evidence for an original Lean definition with an explicit scalar ABI. -/
structure SourceCertificate (Input : Type) (args : Input → List UInt64)
    (source : Input → UInt64) (program : Program) (signatures : Signatures)
    (entry : Nat) where
  body : Expr
  arity : Nat
  admitted : checkProgram program signatures = true
  bodyAt : lookup program entry = some body
  signatureAt : lookup signatures entry =
    some { params := List.replicate arity (.word .w64), result := .word .w64 }
  argsLength : ∀ input, (args input).length = arity
  computes : ∀ input, Runs program body (encodeArgs (args input)) (encodeWord (source input))

end LeanExe.Correct.Scalar64
