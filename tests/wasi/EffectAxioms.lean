import LeanExe.Wasi.RelatedExec
import LeanExe.Wasi.RelatedPrefix
import Verified.Wasi.ReflectLemmas

open Lean Elab Command in
elab "check_effect_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``LeanExe.Wasi.Action.Rel.refl,
    ``LeanExe.Wasi.Action.Rel.mono,
    ``LeanExe.Wasi.Action.Rel.symm,
    ``LeanExe.Wasi.Action.Rel.bind,
    ``LeanExe.Wasi.Action.Rel.map,
    ``LeanExe.Wasi.Action.Rel.of_map_eq,
    ``LeanExe.Wasi.LoopExec.transfer,
    ``LeanExe.Wasi.Action.Rel.exec,
    ``LeanExe.Wasi.Action.Rel.exec_back,
    ``LeanExe.Wasi.Action.Rel.exec_returned_iff,
    ``LeanExe.Wasi.PrefixAdvance.toPrefix,
    ``LeanExe.Wasi.PrefixAdvance.bind,
    ``LeanExe.Wasi.PrefixProgress.bind,
    ``LeanExe.Wasi.PrefixProgress.toPrefix,
    ``LeanExe.Wasi.Prefix.progress,
    ``LeanExe.Wasi.Prefix.progress_iff,
    ``LeanExe.Wasi.Action.Rel.resumeLoop,
    ``LeanExe.Wasi.Action.Rel.advance,
    ``LeanExe.Wasi.PrefixProgress.transfer,
    ``LeanExe.Wasi.Action.Rel.transportPrefix,
    ``LeanExe.Wasi.Action.Rel.transportPrefixBack,
    ``Verified.Wasi.Reflect.unit_eq,
    ``Verified.Wasi.Reflect.ret_eq,
    ``Verified.Wasi.Reflect.bind_eq,
    ``Verified.Wasi.Reflect.read_eq,
    ``Verified.Wasi.Reflect.write_eq,
    ``Verified.Wasi.Reflect.write_value_eq,
    ``Verified.Wasi.Reflect.exit_eq,
    ``Verified.Wasi.Reflect.ite_eq,
    ``Verified.Wasi.Reflect.bind_rel,
    ``Verified.Wasi.Reflect.ite_rel,
    ``Verified.Wasi.Reflect.ite_prop_rel,
    ``Verified.Wasi.Reflect.loop_rel,
    ``Verified.Wasi.Reflect.call_rel]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Effect axiom check passed for {theorems.size} theorems"

check_effect_axioms
