import Verified.Wasi.SyntaxCheck

open Lean Elab Command in
elab "check_wasi_syntax_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Wasm.Encoding.checkInstructionForm_sound,
    ``Wasm.Encoding.checkInstructionForm_complete,
    ``Wasm.Encoding.checkProgramForm_sound,
    ``Wasm.Encoding.checkProgramForm_complete,
    ``Verified.Wasi.checkFragment_sound,
    ``Verified.Wasi.checkFragment_complete,
    ``Verified.Wasi.Relocation.checkProfile_sound,
    ``Verified.Wasi.Relocation.checkProfile_complete,
    ``Verified.Wasi.Command.checkReady_sound,
    ``Verified.Wasi.Command.checkReady_complete,
    ``Verified.Wasi.EffectFunc.checkReady_sound,
    ``Verified.Wasi.EffectFunc.checkReady_complete,
    ``Verified.Wasi.EffectProg.checkReady_sound,
    ``Verified.Wasi.EffectProg.checkReady_complete]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI syntax axiom check passed for {theorems.size} theorems"

check_wasi_syntax_axioms
