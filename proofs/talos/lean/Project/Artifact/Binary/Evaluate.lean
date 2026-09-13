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

theorem code_eq_of_parts
    {start payload bodyStart bodyFinish : Cursor} {size : UInt32}
    {locals : List LocalDecl} {body : List Instr}
    (hsize : Leb.u32 start = .ok (size, payload))
    (hremaining : size.toNat ≤ payload.remaining)
    (hbytes : payload.pos + size.toNat ≤ payload.bytes.size)
    (hlocals : vector localDecl { payload with limit := payload.pos + size.toNat } =
      .ok (locals, bodyStart))
    (hbody : instructionSequenceAt bodyStart.remaining false bodyStart =
      .ok ((body, .end), bodyFinish))
    (hfinish : bodyFinish.pos = payload.pos + size.toNat) :
    code start = .ok (⟨locals, body⟩, { payload with pos := payload.pos + size.toNat }) := by
  have hsequence : instructionSequence bodyStart.remaining false bodyStart =
      .ok ((body, .end), bodyFinish) := hbody
  simp [code, sized, Bind.bind, Pure.pure, Except.bind,
    hsize, bounded, hremaining, hbytes, codeBody, hlocals, expression, hsequence, hfinish]

#print axioms code_eq_of_parts

end Wasm.Binary
