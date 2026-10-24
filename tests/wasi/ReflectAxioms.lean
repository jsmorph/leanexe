import Verified.Wasi.ReflectCommandCases

open Lean Elab Command in
elab "check_wasi_reflection_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked := #[
    ``Verified.Wasi.ReflectCommandCases.callable.calls,
    ``Verified.Wasi.ReflectCommandCases.callable.initial,
    ``Verified.Wasi.ReflectCommandCases.callable.bytes,
    ``Verified.Wasi.ReflectCommandCases.callable.helper.related,
    ``Verified.Wasi.ReflectCommandCases.callable.helper.implements,
    ``Verified.Wasi.ReflectCommandCases.callable.helper.exported,
    ``Verified.Wasi.ReflectCommandCases.callable.helper.total,
    ``Verified.Wasi.ReflectCommandCases.callable.caller.implements,
    ``Verified.Wasi.ReflectCommandCases.callable.borrowBytes.implements,
    ``Verified.Wasi.ReflectCommandCases.callable.ownBytes.implements,
    ``Verified.Wasi.ReflectCommandCases.callable.packetHelper.implements,
    ``Verified.Wasi.ReflectCommandCases.callable.argumentCaller.implements,
    ``Verified.Wasi.ReflectCommandCases.command.calls,
    ``Verified.Wasi.ReflectCommandCases.command.initial,
    ``Verified.Wasi.ReflectCommandCases.command.start,
    ``Verified.Wasi.ReflectCommandCases.command.exported,
    ``Verified.Wasi.ReflectCommandCases.command.total,
    ``Verified.Wasi.ReflectCommandCases.command.bytes]
  for declaration in checked do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"WASI reflection axiom check passed for {checked.size} theorems"

check_wasi_reflection_axioms
