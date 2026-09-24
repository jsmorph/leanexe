import Project.Correct.Scalar64.Certificate
import LeanExe.Correct.Scalar64.Prng
import LeanExe.Correct.Scalar64.Helper

namespace Project.Correct.Scalar64.Pilots
open Wasm
open Project.ProofKit.ScalarTransition

def affine : Function :=
  { arity := 2, localCount := 0, scratch := 2, body := .skip
    result := .bin .add (.bin .add (.bin .mul (.get 0) (.const 3))
      (.bin .mul (.get 1) (.const 2))) (.const 7) }

def affineCertificate : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.Arithmetic.affine input.1 input.2) where
  core := [LeanExe.Correct.Scalar64.affineBody]
  signatures := [LeanExe.Correct.Scalar64.binarySignature]
  coreEntry := 0
  sourceProof := LeanExe.Correct.Scalar64.affineCertificate
  functions := [affine]
  entry := 0
  exportName := "affine"
  function := affine
  found := rfl
  arity := rfl
  admitted := by decide
  lowering := fun (x, y) => ⟨affine.initial [x, y], affine.initial [x, y], .skip, by
    simp [affine, Function.initial, Expr.eval, State.get, U64Op.apply,
      LeanExe.Examples.Arithmetic.affine]⟩

def choose : Function :=
  { arity := 2, localCount := 0, scratch := 2, body := .skip
    result := .ite (.eq (.get 0) (.const 0)) (.bin .add (.get 1) (.const 1))
      (.bin .add (.get 0) (.get 1)) }

def chooseCertificate : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.Arithmetic.choose input.1 input.2) where
  core := [LeanExe.Correct.Scalar64.chooseBody]
  signatures := [LeanExe.Correct.Scalar64.binarySignature]
  coreEntry := 0
  sourceProof := LeanExe.Correct.Scalar64.chooseCertificate
  functions := [choose]
  entry := 0
  exportName := "choose"
  function := choose
  found := rfl
  arity := rfl
  admitted := by decide
  lowering := fun (x, y) => ⟨choose.initial [x, y], choose.initial [x, y], .skip, by
    by_cases h : x = 0 <;>
      simp [choose, Function.initial, Expr.eval, State.get, U64Op.apply,
        LeanExe.Examples.Arithmetic.choose, h]⟩

def mixFirst : Expr .u64 :=
  .bin .mul (.bin .bitXor (.get 0) (.bin .shiftRight (.get 0) (.const 30)))
    (.const 0xbf58476d1ce4e5b9)
def mixSecond : Expr .u64 :=
  .bin .mul (.bin .bitXor (.get 1) (.bin .shiftRight (.get 1) (.const 27)))
    (.const 0x94d049bb133111eb)
def mix : Function :=
  { arity := 1, localCount := 2, scratch := 3
    body := .seq (.assign 1 mixFirst) (.assign 2 mixSecond)
    result := .bin .bitXor (.get 2) (.bin .shiftRight (.get 2) (.const 31)) }

def mixCertificate : Certificate UInt64 (fun state => [state]) LeanExe.Examples.Prng.mix where
  core := [LeanExe.Correct.Scalar64.mixBody]
  signatures := [LeanExe.Correct.Scalar64.unarySignature]
  coreEntry := 0
  sourceProof := LeanExe.Correct.Scalar64.mixCertificate
  functions := [mix]
  entry := 0
  exportName := "mix"
  function := mix
  found := rfl
  arity := rfl
  admitted := by decide
  lowering := by
    intro state
    let z1 := (state ^^^ (state >>> 30)) * 0xbf58476d1ce4e5b9
    let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
    let initial := mix.initial [state]
    let middle : State := { params := [.i64 state], locals := [.i64 z1, .i64 0] }
    let final : State := { params := [.i64 state], locals := [.i64 z1, .i64 z2] }
    refine ⟨final, final, ?_, ?_⟩
    · apply Executes.seq (middle := middle)
      · apply Executes.assign (value := z1) (afterValue := initial)
        · simp [mix, mixFirst, initial, Function.initial, Expr.eval, State.get, U64Op.apply, z1]
        · rfl
      · apply Executes.assign (value := z2) (afterValue := middle)
        · simp [mix, mixSecond, middle, Expr.eval, State.get, U64Op.apply, z2]
        · rfl
    · simp [mix, final, Expr.eval, State.get, U64Op.apply, z1, z2, LeanExe.Examples.Prng.mix]

def combine : Function :=
  { arity := 2, localCount := 0, scratch := 2, body := .skip
    result := .bin .add (.bin .mul (.get 0) (.const 5)) (.get 1) }
def helper : Function :=
  { arity := 2, localCount := 1, scratch := 3
    body := .call 2 0 [.bin .add (.get 0) (.const 1), .bin .mul (.get 1) (.const 2)]
    result := .bin .add (.get 2) (.get 0) }

def helperCertificate : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.ScalarHelper.caller input.1 input.2) where
  core := [LeanExe.Correct.Scalar64.combineBody, LeanExe.Correct.Scalar64.helperBody]
  signatures := [LeanExe.Correct.Scalar64.binarySignature, LeanExe.Correct.Scalar64.binarySignature]
  coreEntry := 1
  sourceProof := LeanExe.Correct.Scalar64.helperCertificate
  functions := [combine, helper]
  entry := 1
  exportName := "helper"
  function := helper
  found := rfl
  arity := rfl
  admitted := by decide
  lowering := by
    intro (x, y)
    let value := LeanExe.Examples.ScalarHelper.combine (x + 1) (y * 2)
    let initial := helper.initial [x, y]
    let callee := combine.initial [x + 1, y * 2]
    let final : State := { params := [.i64 x, .i64 y], locals := [.i64 value] }
    refine ⟨final, final, ?_, ?_⟩
    · apply Executes.call (args := [x + 1, y * 2]) (afterArgs := initial)
        (function := combine) (afterBody := callee) (result := value) (afterResult := callee)
      · simp [helper, initial, Function.initial, evalArgs, Expr.eval, State.get, U64Op.apply]
      · rfl
      · rfl
      · exact .skip
      · simp [combine, callee, Function.initial, Expr.eval, State.get, U64Op.apply,
          value, LeanExe.Examples.ScalarHelper.combine]
      · rfl
    · simp [helper, final, Expr.eval, State.get, U64Op.apply,
        value, LeanExe.Examples.ScalarHelper.caller]

end Project.Correct.Scalar64.Pilots
