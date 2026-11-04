import Demos.Gpt32.NativeCases

open Demos.Gpt32

def main : List String → IO Unit
  | [target, host, dir] =>
    match Target.ofString? target with
    | some t => NativeCases.run t host dir
    | none => throw <| IO.userError s!"unknown target: {target}"
  | _ => throw <| IO.userError "usage: VerifiedNative.lean TARGET HOST DIR"
