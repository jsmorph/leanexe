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

private def codeRanges (bytes : ByteArray) : Except Error (List String) := do
  let mut cursor ← codeStart bytes 0
  let mut result := []
  for index in [:bytes.size] do
    if cursor.pos == cursor.limit then return result.reverse
    let (_, next) ← code cursor
    result := s!"{index},{cursor.pos},{next.pos},{cursor.limit}" :: result
    cursor := next
  throw { offset := cursor.pos, kind := .malformed "code count exceeds input size" }

private def offsetsAt (start : Cursor) : Except Error (List String) := do
  let (size, first) ← Leb.u32 start
  let stop := first.pos + size.toNat
  let (_, body) ← vector localDecl { first with limit := stop }
  let mut cursor := body
  let mut fuel := body.remaining
  let mut result := [s!"code,{start.pos},{stop},{body.pos},{first.pos}"]
  for i in [:body.remaining] do
    result := s!"{i},{fuel},{cursor.pos}" :: result
    let (next, _) ← Parser.peekByte cursor
    if next == 11 then
      return result.reverse
    let (_, tail) ← instruction (fuel - 1) cursor
    cursor := tail
    fuel := fuel - 1
  throw { offset := cursor.pos, kind := .malformed "unterminated function body" }

private def nestedOffsets : Nat → Nat → Bool → Cursor → String → Except Error (List String)
  | 0, _, _, start, _ =>
      throw { offset := start.pos, kind := .malformed "metadata nesting exceeds input size" }
  | depth + 1, initialFuel, allowElse, start, path => do
      let ((_, terminator), finish) ← instructionSequence initialFuel allowElse start
      let ending := match terminator with | .end => "end" | .otherwise => "otherwise"
      let mut result := [s!"seq,{path},{start.pos},{initialFuel},{allowElse},{finish.pos},{ending},{start.limit}"]
      let mut cursor := start
      let mut fuel := initialFuel
      for i in [:start.remaining] do
        result := result ++ [s!"at,{path},{i},{fuel},{cursor.pos}"]
        let (nextByte, _) ← Parser.peekByte cursor
        if nextByte == 11 || nextByte == 5 then return result
        let (item, next) ← instruction (fuel - 1) cursor
        match item with
        | .block _ _ | .loop _ _ | .iff _ _ _ =>
            let (_, afterOpcode) ← Parser.readByte cursor
            let (_, nestedStart) ← blockType afterOpcode
            let isIf := match item with | .iff _ _ _ => true | _ => false
            result := result ++ (← nestedOffsets depth (fuel - 2) isIf nestedStart s!"{path}.{i}.t")
            if isIf then
              let ((_, ending), afterThen) ← instructionSequence (fuel - 2) true nestedStart
              match ending with
              | .end => pure ()
              | .otherwise =>
                  result := result ++ (← nestedOffsets depth (fuel - 2) false afterThen s!"{path}.{i}.e")
        | _ => pure ()
        cursor := next
        fuel := fuel - 1
      throw { offset := cursor.pos, kind := .malformed "unterminated metadata sequence" }

private def allOffsets (bytes : ByteArray) (nested : Bool := false) : Except Error (List String) := do
  let mut cursor ← codeStart bytes 0
  let mut result := []
  for index in [:bytes.size] do
    if cursor.pos == cursor.limit then return result.reverse
    for line in ← offsetsAt cursor do
      result := s!"{index},{line}" :: result
    if nested then
      let (size, first) ← Leb.u32 cursor
      let (_, body) ← vector localDecl { first with limit := first.pos + size.toNat }
      for line in ← nestedOffsets bytes.size body.remaining false body s!"{index}" do
        result := line :: result
    let (_, next) ← code cursor
    cursor := next
  throw { offset := cursor.pos, kind := .malformed "code count exceeds input size" }

def main (args : List String) : IO UInt32 := do
  let (path, indexText, output) ← match args with
    | [path, indexText] => pure (path, indexText, none)
    | [path, indexText, output] => pure (path, indexText, some output)
    | _ => throw (IO.userError "usage: CodeOffsets <program.wasm> <function-index | --codes | --all-offsets | --nested> [fresh-output]")
  if let some output := output then
    if ← System.FilePath.pathExists output then
      throw (IO.userError s!"output already exists: {output}")
  let bytes ← IO.FS.readBinFile path
  let result ← if indexText == "--codes" then pure (codeRanges bytes)
    else if indexText == "--all-offsets" then pure (allOffsets bytes) else do
      if indexText == "--nested" then pure (allOffsets bytes true) else do
        let some index := indexText.toNat? | throw (IO.userError "invalid function index")
        pure (do offsetsAt (← codeStart bytes index))
  match result with
  | .error error => throw (IO.userError s!"{path}:{error.offset}: {repr error.kind}")
  | .ok lines =>
      match output with
      | none => for line in lines do IO.println line
      | some output => IO.FS.writeFile output (String.intercalate "\n" lines ++ "\n")
      pure 0
