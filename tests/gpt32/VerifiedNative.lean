import Demos.Gpt32.NativeCases
import Demos.Gpt32.VerifiedKernels

def main : List String → IO Unit
  | [host, dir] => Demos.Gpt32.NativeCases.run host dir Demos.Gpt32.Verified.kernelMap
  | _ => throw <| IO.userError "usage: VerifiedNative.lean HOST DIR"
