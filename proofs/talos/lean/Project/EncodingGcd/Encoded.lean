import Project.EncodingGcd.Spec
import Project.Encoding

namespace Project.EncodingGcd

open Wasm

theorem module_correct : Spec.GcdSpecFor «module» := Spec.gcd_correct

theorem encoded_correct (bytes : ByteArray)
    (success : Wasm.Encoding.encode «module» = .ok bytes) :
    Wasm.Encoding.Encodes «module» bytes ∧
      Wasm.Encoding.Represents Spec.GcdSpecFor bytes := by
  have encoding := Wasm.Encoding.encode_correct «module» bytes success
  exact ⟨encoding, «module», encoding, module_correct⟩

end Project.EncodingGcd

def main (args : List String) : IO Unit :=
  match args with
  | [path] => Wasm.Encoding.writeModule path Project.EncodingGcd.«module»
  | _ => throw (IO.userError "expected a WASM output path")
