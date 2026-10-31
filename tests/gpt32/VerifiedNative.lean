import Demos.Gpt32.NativeCases

def main : List String → IO Unit
  | [host, dir] => Demos.Gpt32.NativeCases.run host dir
  | _ => throw <| IO.userError "usage: VerifiedNative.lean HOST DIR"
