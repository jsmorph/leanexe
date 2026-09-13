import Project.Artifact.Binary.Decode

open Wasm.Binary

private def codeStart (bytes : ByteArray) (index : Nat) : Except Error Cursor := do
  let mut cursor : Cursor := { bytes, pos := 8, limit := bytes.size }
  for _ in [:bytes.size] do
    let (id, afterId) ← Parser.readByte cursor
    let (size, payload) ← Leb.u32 afterId
    let stop := payload.pos + size.toNat
    if id == 10 then
      let (count, first) ← Leb.u32 { payload with limit := stop }
      if index ≥ count.toNat then
        throw { offset := first.pos, kind := .malformed "function index exceeds code count" }
      cursor := first
      for _ in [:index] do
        let (_, next) ← code cursor
        cursor := next
      return cursor
    cursor := { payload with pos := stop }
  throw { offset := cursor.pos, kind := .malformed "code section absent" }

private def offsets (bytes : ByteArray) (index : Nat) : Except Error (List String) := do
  let start ← codeStart bytes index
  let (size, first) ← Leb.u32 start
  let stop := first.pos + size.toNat
  let (_, body) ← vector localDecl { first with limit := stop }
  let mut cursor := body
  let mut fuel := body.remaining
  let mut result := [s!"code,{start.pos},{stop},{body.pos}"]
  for i in [:body.remaining] do
    result := s!"{i},{fuel},{cursor.pos}" :: result
    let (next, _) ← Parser.peekByte cursor
    if next == 11 then
      return result.reverse
    let (_, tail) ← instruction (fuel - 1) cursor
    cursor := tail
    fuel := fuel - 1
  throw { offset := cursor.pos, kind := .malformed "unterminated function body" }

def main (args : List String) : IO UInt32 := do
  let [path, indexText] := args
    | throw (IO.userError "usage: CodeOffsets <program.wasm> <function-index>")
  let some index := indexText.toNat?
    | throw (IO.userError "invalid function index")
  let bytes ← IO.FS.readBinFile path
  match offsets bytes index with
  | .error error => throw (IO.userError s!"{path}:{error.offset}: {repr error.kind}")
  | .ok lines =>
      for line in lines do IO.println line
      pure 0
