import Project.ProofKit.I64Frame

namespace Project.ProofKit
open Wasm

theorem Frame.local_of_take_eq {before after : Locals} {count index : Nat}
    (hPrefix : after.locals.take count = before.locals.take count) (hIndex : index < count) :
    after.locals[index]? = before.locals[index]? := by
  have h := congrArg (fun values => values[index]?) hPrefix
  simpa only [List.getElem?_take_of_lt hIndex] using h

#print axioms Frame.local_of_take_eq

end Project.ProofKit
