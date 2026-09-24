import Project.ByteIO.Binary
import Project.Artifact.Binary.CodeParts

namespace Project.ByteIO.Binary
open Wasm.Binary Wasm.Binary.Parser

theorem parseSection_eq_of_parts {id : UInt8} {entry : Parser α}
    {start payload finish : Cursor} {entries : List α}
    (hid : expectByte id start = .ok ((), payload))
    (hbody : sized (vector entry) payload = .ok (entries, finish)) :
    parseSection id entry start = .ok (entries, finish) := by
  simp [parseSection, Bind.bind, Pure.pure, Parser.instMonad, Except.bind, hid, hbody]

#print axioms parseSection_eq_of_parts
end Project.ByteIO.Binary
