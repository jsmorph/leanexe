import Project.Artifact.Binary.Evaluate

namespace Wasm.Binary
open Parser

def Instr.childBody (instruction : Instr) (alternative : Bool) : List Instr :=
  match instruction with
  | .block _ body | .loop _ body => body
  | .iff _ body other => if alternative then other.getD [] else body
  | _ => []

theorem vectorLoop_eq_cons {parser : Parser α} {count : Nat}
    {start middle finish : Cursor} {head : α} {tail : List α}
    (hhead : parser start = .ok (head, middle))
    (htail : Internal.vectorLoop parser count middle = .ok (tail, finish)) :
    Internal.vectorLoop parser (count + 1) start = .ok (head :: tail, finish) := by
  simp [Internal.vectorLoop, Bind.bind, Pure.pure, Except.bind, hhead, htail]

theorem vector_eq_of_parts {parser : Parser α} {length : UInt32}
    {start itemsStart finish : Cursor} {values : List α}
    (hlength : Leb.u32 start = .ok (length, itemsStart))
    (hfits : length.toNat ≤ itemsStart.remaining)
    (hitems : Internal.vectorLoop parser length.toNat itemsStart = .ok (values, finish)) :
    vector parser start = .ok (values, finish) := by
  simp [vector, Bind.bind, Except.bind, hlength, hfits, hitems]

theorem sized_eq_of_parts {parser : Parser α} {size : UInt32}
    {start payload finish : Cursor} {value : α}
    (hsize : Leb.u32 start = .ok (size, payload))
    (hremaining : size.toNat ≤ payload.remaining)
    (hbytes : payload.pos + size.toNat ≤ payload.bytes.size)
    (hbody : parser { payload with limit := payload.pos + size.toNat } = .ok (value, finish))
    (hfinish : finish.pos = payload.pos + size.toNat) :
    sized parser start = .ok (value, { payload with pos := payload.pos + size.toNat }) := by
  simp [sized, Bind.bind, Except.bind, hsize, bounded, hremaining, hbytes, hbody, hfinish]

#print axioms vectorLoop_eq_cons
#print axioms vector_eq_of_parts
#print axioms sized_eq_of_parts

end Wasm.Binary
