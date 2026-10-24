import LeanExe.Encoding.ValidityProof
import Verified.Wasi.ReflectCommandCases

open Lean Elab Command in
elab "check_wasi_validity_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Wasm.Encoding.ValidityProof.globalReady_of_spec,
    ``Wasm.Encoding.ValidityProof.checkGlobal_sound,
    ``Wasm.Encoding.ValidityProof.functions_of_indices,
    ``Wasm.Encoding.ValidityProof.types_nil,
    ``Wasm.Encoding.ValidityProof.types_cons,
    ``Wasm.Encoding.ValidityProof.checkDataSegment_sound,
    ``Wasm.Encoding.ValidityProof.checkMemory_sound,
    ``Wasm.Encoding.ValidityProof.checkMemories_sound,
    ``Wasm.Encoding.ValidityProof.checkImports_sound,
    ``Verified.Wasi.ReflectCommandCases.callable.validity,
    ``Verified.Wasi.ReflectCommandCases.command.validity,
    ``Verified.Wasi.ReflectCommandCases.callable.validBinary,
    ``Verified.Wasi.ReflectCommandCases.command.validBinary,
    ``Verified.Wasi.ReflectCommandCases.callable.bytes,
    ``Verified.Wasi.ReflectCommandCases.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI validity axiom check passed for {theorems.size} theorems"

check_wasi_validity_axioms
