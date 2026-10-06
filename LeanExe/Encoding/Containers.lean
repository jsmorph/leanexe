import LeanExe.Encoding.Values

namespace Wasm.Encoding

abbrev Encoded (relation : Spec.Bytes → α → Prop) (value : α) :=
  { bytes : Spec.Bytes // relation bytes value }

abbrev Result (relation : Spec.Bytes → α → Prop) (value : α) :=
  Except String (Encoded relation value)

def u32 (value : Nat) : Result (Spec.Unsigned 32) value :=
  if fits : value < 2 ^ 32 then
    .ok ⟨unsigned 32 value, unsigned_correct 32 value (by decide) fits⟩
  else .error "integer exceeds the WASM u32 limit"

def items (encode : (value : α) → Result relation value) :
    (values : List α) → Result (Spec.Items relation) values
  | [] => .ok ⟨[], .nil⟩
  | head :: tail => do
      let first ← encode head
      let rest ← items encode tail
      pure ⟨first.val ++ rest.val, .cons _ _ _ _ first.property rest.property⟩

def vector (encode : (value : α) → Result relation value)
    (values : List α) : Result (Spec.Vector relation) values := do
  let count ← u32 values.length
  let body ← items encode values
  pure ⟨count.val ++ body.val, .intro _ _ _ count.property body.property⟩

def sized (payload : Encoded relation value) : Result (Spec.Sized relation) value := do
  let count ← u32 payload.val.length
  pure ⟨count.val ++ payload.val, .intro _ _ _ count.property payload.property⟩

def name (value : String) : Result Spec.Name value := do
  let count ← u32 value.toUTF8.size
  pure ⟨count.val ++ value.toUTF8.data.toList, .intro _ _ count.property⟩

end Wasm.Encoding
