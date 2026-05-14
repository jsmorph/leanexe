import LeanExe.Ascii.Json

namespace LeanExe
namespace Ascii
namespace Json

mutual
inductive Value where
  | null : Value
  | bool : Bool -> Value
  | num : UInt64 -> Value
  | str : AsciiString -> Value
  | arr : Array Value -> Value
  | obj : Array Field -> Value

inductive Field where
  | mk : AsciiString -> Value -> Field
end

instance : Inhabited Value :=
  ⟨Value.null⟩

instance : Inhabited Field :=
  ⟨Field.mk (AsciiString.ofTrustedByteArray ByteArray.empty) Value.null⟩

structure ParsedValue where
  pos : Nat
  value : Value

structure ParsedArray where
  pos : Nat
  items : Array Value

structure ParsedObject where
  pos : Nat
  fields : Array Field

inductive ParseRequest where
  | value : ParseRequest
  | array : Array Value -> Bool -> ParseRequest
  | object : Array Field -> Bool -> ParseRequest

inductive ParseResult where
  | value : ParsedValue -> ParseResult
  | array : ParsedArray -> ParseResult
  | object : ParsedObject -> ParseResult

def ParseResult.value? : ParseResult -> Option ParsedValue
  | ParseResult.value parsed => some parsed
  | ParseResult.array _ => none
  | ParseResult.object _ => none

def ParseResult.array? : ParseResult -> Option ParsedArray
  | ParseResult.value _ => none
  | ParseResult.array parsed => some parsed
  | ParseResult.object _ => none

def ParseResult.object? : ParseResult -> Option ParsedObject
  | ParseResult.value _ => none
  | ParseResult.array _ => none
  | ParseResult.object parsed => some parsed

def parseFuel (text : AsciiString) : Nat :=
  text.size + 1

def parseAnyFuel : Nat -> ParseRequest -> AsciiString -> Nat -> Option ParseResult
  | 0, _request, _text, _pos => none
  | fuel + 1, request, text, pos =>
      match request with
      | ParseRequest.value =>
          let start := skipWs text pos
          let byte := text.getD start 0
          if byte == byteQuote then
            match parseStringAt text start with
            | some parsed =>
                some (ParseResult.value { pos := parsed.pos, value := Value.str parsed.value })
            | none => none
          else if byte == byteLBracket then
            match parseAnyFuel fuel (ParseRequest.array Array.empty true) text (start + 1) with
            | some result =>
                match result.array? with
                | some parsed =>
                    some (ParseResult.value { pos := parsed.pos, value := Value.arr parsed.items })
                | none => none
            | none => none
          else if byte == byteLBrace then
            match parseAnyFuel fuel (ParseRequest.object Array.empty true) text (start + 1) with
            | some result =>
                match result.object? with
                | some parsed =>
                    some (ParseResult.value { pos := parsed.pos, value := Value.obj parsed.fields })
                | none => none
            | none => none
          else if byte == byteT then
            match expectBytes text start literalTrue with
            | some next =>
                some (ParseResult.value { pos := next, value := Value.bool true })
            | none => none
          else if byte == byteF then
            match expectBytes text start literalFalse with
            | some next =>
                some (ParseResult.value { pos := next, value := Value.bool false })
            | none => none
          else if byte == byteN then
            match expectBytes text start literalNull with
            | some next =>
                some (ParseResult.value { pos := next, value := Value.null })
            | none => none
          else if isDigit byte then
            match parseUInt64 text start with
            | some parsed =>
                some (ParseResult.value { pos := parsed.pos, value := Value.num parsed.value })
            | none => none
          else
            none
      | ParseRequest.array items canEnd =>
          let pos0 := skipWs text pos
          if pos0 < text.size && text.get! pos0 == byteRBracket then
            if canEnd then
              some (ParseResult.array { pos := pos0 + 1, items := items })
            else
              none
          else
            match parseAnyFuel fuel ParseRequest.value text pos0 with
            | none => none
            | some result =>
                match result.value? with
                | none => none
                | some parsed =>
                    let nextItems := items.push parsed.value
                    let afterValue := skipWs text parsed.pos
                    if afterValue < text.size && text.get! afterValue == byteComma then
                      parseAnyFuel fuel (ParseRequest.array nextItems false) text (afterValue + 1)
                    else if afterValue < text.size && text.get! afterValue == byteRBracket then
                      some (ParseResult.array { pos := afterValue + 1, items := nextItems })
                    else
                      none
      | ParseRequest.object fields canEnd =>
          let pos0 := skipWs text pos
          if pos0 < text.size && text.get! pos0 == byteRBrace then
            if canEnd then
              some (ParseResult.object { pos := pos0 + 1, fields := fields })
            else
              none
          else
            match parseStringAt text pos0 with
            | none => none
            | some name =>
                match expectWsByte text name.pos byteColon with
                | none => none
                | some afterColon =>
                    match parseAnyFuel fuel ParseRequest.value text afterColon with
                    | none => none
                    | some result =>
                        match result.value? with
                        | none => none
                        | some parsed =>
                            let nextFields := fields.push (Field.mk name.value parsed.value)
                            let afterValue := skipWs text parsed.pos
                            if afterValue < text.size && text.get! afterValue == byteComma then
                              parseAnyFuel fuel (ParseRequest.object nextFields false) text (afterValue + 1)
                            else if afterValue < text.size && text.get! afterValue == byteRBrace then
                              some (ParseResult.object { pos := afterValue + 1, fields := nextFields })
                            else
                              none

def parseValueFuel (fuel : Nat) (text : AsciiString) (pos : Nat) : Option ParsedValue :=
  match parseAnyFuel fuel ParseRequest.value text pos with
  | some result => result.value?
  | none => none

def parseArrayFuel (fuel : Nat) (text : AsciiString) (pos : Nat) (items : Array Value)
    (canEnd : Bool) : Option ParsedArray :=
  match parseAnyFuel fuel (ParseRequest.array items canEnd) text pos with
  | some result => result.array?
  | none => none

def parseObjectFuel (fuel : Nat) (text : AsciiString) (pos : Nat) (fields : Array Field)
    (canEnd : Bool) : Option ParsedObject :=
  match parseAnyFuel fuel (ParseRequest.object fields canEnd) text pos with
  | some result => result.object?
  | none => none

def parse (text : AsciiString) : Option Value :=
  match parseValueFuel (parseFuel text) text 0 with
  | some parsed =>
      if skipWs text parsed.pos == text.size then
        some parsed.value
      else
        none
  | none => none

def parseBytes (bytes : ByteArray) : Option Value :=
  match AsciiString.ofByteArray? bytes with
  | some text => parse text
  | none => none

def Field.name : Field -> AsciiString
  | Field.mk name _value => name

def Field.value : Field -> Value
  | Field.mk _name value => value

def asUInt64? : Value -> Option UInt64
  | Value.null => none
  | Value.bool _ => none
  | Value.num value => some value
  | Value.str _ => none
  | Value.arr _ => none
  | Value.obj _ => none

def asBool? : Value -> Option Bool
  | Value.null => none
  | Value.bool value => some value
  | Value.num _ => none
  | Value.str _ => none
  | Value.arr _ => none
  | Value.obj _ => none

def asArray? : Value -> Option (Array Value)
  | Value.null => none
  | Value.bool _ => none
  | Value.num _ => none
  | Value.str _ => none
  | Value.arr items => some items
  | Value.obj _ => none

def asObject? : Value -> Option (Array Field)
  | Value.null => none
  | Value.bool _ => none
  | Value.num _ => none
  | Value.str _ => none
  | Value.arr _ => none
  | Value.obj fields => some fields

def asString? : Value -> Option AsciiString
  | Value.null => none
  | Value.bool _ => none
  | Value.num _ => none
  | Value.str value => some value
  | Value.arr _ => none
  | Value.obj _ => none

def getFieldFuel : Nat -> Array Field -> AsciiString -> Nat -> Option Value
  | 0, _fields, _name, _index => none
  | fuel + 1, fields, name, index =>
      if index == fields.size then
        none
      else
        let field := fields[index]!
        if (Field.name field).equals name then
          some (Field.value field)
        else
          getFieldFuel fuel fields name (index + 1)

def get? (value : Value) (name : AsciiString) : Option Value :=
  match value with
  | Value.null => none
  | Value.bool _ => none
  | Value.num _ => none
  | Value.str _ => none
  | Value.arr _ => none
  | Value.obj fields => getFieldFuel (fields.size + 1) fields name 0

structure RenderState where
  failed : Bool
  first : Bool
  out : ByteArray

def separatedAppend (state : RenderState) (bytes : ByteArray) : RenderState :=
  if state.failed then
    state
  else
    let out := if state.first then state.out else state.out.push byteComma
    { failed := false, first := false, out := out.append bytes }

def failRender (state : RenderState) : RenderState :=
  { state with failed := true }

def finishRender (state : RenderState) (closing : UInt8) : Option ByteArray :=
  if state.failed then
    none
  else
    some (state.out.push closing)

mutual
def render? : Value -> Option ByteArray
  | Value.null => some literalNull
  | Value.bool value =>
      if value then
        some literalTrue
      else
        some literalFalse
  | Value.num value => some (appendUInt64Decimal ByteArray.empty value)
  | Value.str value => appendQuotedString? ByteArray.empty value
  | Value.arr items =>
      let state :=
        items.foldl
          (fun state item =>
            if state.failed then
              state
            else
              match render? item with
              | some bytes => separatedAppend state bytes
              | none => failRender state)
          { failed := false, first := true, out := ByteArray.empty.push byteLBracket }
      finishRender state byteRBracket
  | Value.obj fields =>
      let state :=
        fields.foldl
          (fun state field =>
            if state.failed then
              state
            else
              match renderField? field with
              | some bytes => separatedAppend state bytes
              | none => failRender state)
          { failed := false, first := true, out := ByteArray.empty.push byteLBrace }
      finishRender state byteRBrace

def renderField? : Field -> Option ByteArray
  | Field.mk name value =>
      match appendQuotedString? ByteArray.empty name with
      | none => none
      | some out =>
          match render? value with
          | some rendered => some ((out.push byteColon).append rendered)
          | none => none
end

def render (value : Value) : ByteArray :=
  match render? value with
  | some bytes => bytes
  | none => errorJson

def object1Value (name : AsciiString) (value : Value) : Value :=
  Value.obj #[Field.mk name value]

end Json
end Ascii
end LeanExe
