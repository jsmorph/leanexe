import Project.Artifact.Binary.Decode
import Lean.Elab.Tactic.Cbv
import Lean.Elab.Tactic.CbvSimproc

namespace Wasm.Binary
open Parser

attribute [cbv_opaque] instructionSequence

@[cbv_opaque] def instructionSequenceAt (fuel : Nat) (allowElse : Bool) (cursor : Cursor) :
    Except Error ((List Instr × Terminator) × Cursor) :=
  instructionSequence fuel allowElse cursor

@[cbv_eval] theorem instructionSequence_eta (fuel : Nat) (allowElse : Bool) :
    instructionSequence fuel allowElse = fun cursor => instructionSequenceAt fuel allowElse cursor := rfl

@[cbv_eval] theorem instructionSequenceAt_apply (fuel : Nat) (allowElse : Bool) (cursor : Cursor) :
    instructionSequenceAt fuel allowElse cursor =
      (match fuel with
      | 0 => fail (.malformed "unterminated instruction sequence")
      | fuel + 1 => do
          let next ← peekByte
          if next = 11 then
            let _ ← readByte
            pure ([], Terminator.end)
          else if next = 5 then
            if allowElse then
              let _ ← readByte
              pure ([], Terminator.otherwise)
            else
              fail (.malformed "unexpected else")
          else
            let first ← instruction fuel
            let (rest, terminator) ← instructionSequence fuel allowElse
            pure (first :: rest, terminator)) cursor := by
  cases fuel <;> rfl

#print axioms instructionSequenceAt_apply

open Lean Meta Sym Simp in
cbv_simproc cbv_eval reuseInstructionSequence (instructionSequenceAt _ _ _) := fun e => do
  let some rules ← Tactic.Cbv.getCbvEvalLemmas ``instructionSequenceAt | return .rfl
  for rule in rules.getMatch (← getMCtx) e do
    if rule.pattern.varTypes.isEmpty then
      let result ← rule.rewrite e
      if !result.isRfl then return result
  return .rfl

end Wasm.Binary
