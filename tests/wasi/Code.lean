import Verified.Bytes.Code
import LeanExe.Encoding.Instructions

open Verified.Bytes Wasm.Encoding

def encodable (code : Wasm.Program) : Bool :=
  match program code with
  | .ok _ => true
  | .error _ => false

#guard encodable (getCode 0 1 2)
#guard encodable (copyByteCode 0 1 2)
#guard encodable (copyCode 0 1 2 3)
#guard encodable (copyOwnedCode 0 1 2)
