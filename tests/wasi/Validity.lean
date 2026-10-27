import LeanExe.Encoding.ValidityProof
import LeanExe.Encoding.FormCheck

namespace WasiValidityTest

open Lean Meta Elab Term

private def context : Wasm.Encoding.Spec.Validity.Context :=
  { functions := [], locals := [], globals := [], labels := [[]], results := [], hasMemory := false }

private def expectRejection (label : String) (code : Wasm.Program) (termSyntax : Syntax)
    (outputs : List Wasm.ValueType) (expected : String) : TermElabM Unit := do
  let expression ← Term.elabTerm termSyntax (some (mkConst ``Wasm.Program))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let rejected ← try
      discard (Wasm.Encoding.ValidityProof.program context (mkConst ``context) code expression [] outputs)
      pure false
    catch
    | .error _ message =>
      let actual ← message.toString
      if actual.startsWith expected then pure true
      else throwError "{label}: expected error beginning {expected}, received {actual}"
    | exception => throw exception
  unless rejected do throwError "{label}: the malformed body was accepted"

example : Wasm.Encoding.ProgramForm [.constI64 7, .eqz] :=
  Wasm.Encoding.checkProgramForm_sound (by decide +kernel)

run_elab do
  expectRejection "operand stack mismatch" [.constI64 7, .eqz]
    (← `([Wasm.Instruction.constI64 7, Wasm.Instruction.eqz])) [.i32]
    "validity proof: operand types disagree:"
  expectRejection "missing local" [.localGet 0]
    (← `([Wasm.Instruction.localGet 0])) [.i64]
    "validity proof: local index 0 is out of bounds"
  expectRejection "missing function" [.call 0]
    (← `([Wasm.Instruction.call 0])) []
    "validity proof: function index 0 is out of bounds"
  expectRejection "missing branch label" [.br 1]
    (← `([Wasm.Instruction.br 1])) []
    "validity proof: label index 1 is out of bounds"

end WasiValidityTest
