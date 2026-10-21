import Examples.Gpt32.NativeCases
import Verified.Examples.Gpt32Kernels

def main : List String → IO Unit
  | [host, dir] => Examples.Gpt32.NativeCases.run host dir Verified.Examples.Gpt32.kernelMap
  | _ => throw <| IO.userError "usage: VerifiedNative.lean HOST DIR"
