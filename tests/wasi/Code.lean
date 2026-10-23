import Verified.Bytes.Code
import Verified.Bytes.BuildCode
import Verified.Bytes.LiteralCode
import Verified.Wasi.WrapperCode
import Verified.Wasi.ReadCode
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
#guard encodable (buildCode 0 1 2 [.localGet 2])
#guard encodable (literalCode 4096 [0, 255] 0)
#guard encodable (Verified.Wasi.writeCode .stdout 0 1 2)
#guard encodable (Verified.Wasi.writeCode .stderr 0 1 2)
#guard encodable (Verified.Wasi.exitCode 0)
#guard encodable (Verified.Wasi.readCallCode 0 1)
#guard encodable (Verified.Wasi.discardReadCode 0)
#guard encodable (Verified.Wasi.readCode 0 1 2 3)
