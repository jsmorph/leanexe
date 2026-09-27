import LeanExe.Ascii.Decimal

namespace LeanExe
namespace Ascii
namespace Json

def expectFieldName1 (text : AsciiString) (pos : Nat) (name : UInt8) : Option Nat :=
  match expectWsByte text pos byteQuote with
  | none => none
  | some pos1 =>
      match expectByte text pos1 name with
      | none => none
      | some pos2 =>
          match expectByte text pos2 byteQuote with
          | none => none
          | some pos3 => expectWsByte text pos3 byteColon

def expectBytesFuel : Nat -> AsciiString -> Nat -> ByteArray -> Nat -> Option Nat
  | 0, _text, _pos, _name, _index => none
  | fuel + 1, text, pos, name, index =>
      if !(index == name.size) && pos < text.size && text.get! pos == name.get! index then
        expectBytesFuel fuel text (pos + 1) name (index + 1)
      else
        if index == name.size then
          some pos
        else
          none

def expectBytes (text : AsciiString) (pos : Nat) (name : ByteArray) : Option Nat :=
  expectBytesFuel (name.size + 1) text pos name 0

def expectFieldName (text : AsciiString) (pos : Nat) (name : ByteArray) : Option Nat :=
  match expectWsByte text pos byteQuote with
  | none => none
  | some pos1 =>
      match expectBytes text pos1 name with
      | none => none
      | some pos2 =>
          match expectByte text pos2 byteQuote with
          | none => none
          | some pos3 => expectWsByte text pos3 byteColon

def errorJson : ByteArray :=
  "{\"error\":1}".toUTF8

structure ParsedString where
  pos : Nat
  value : AsciiString

structure FieldRange where
  start : Nat
  stop : Nat
deriving Inhabited

structure CompositeScanState where
  pos : Nat
  depth : Nat
  failed : Bool

structure FieldSearchState where
  pos : Nat
  done : Bool
  failed : Bool
  found : Bool
  start : Nat
  stop : Nat

structure ArrayRangeState where
  pos : Nat
  canEnd : Bool
  done : Bool
  failed : Bool
  ranges : Array FieldRange

def literalTrue : ByteArray :=
  "true".toUTF8

def literalFalse : ByteArray :=
  "false".toUTF8

def literalNull : ByteArray :=
  "null".toUTF8

def isJsonBareStringByte (byte : UInt8) : Bool :=
  let value := byte.toUInt64
  !(value < (32 : UInt64)) &&
    value < (128 : UInt64) &&
    !(byte == byteQuote) &&
    !(byte == byteBackslash)

def parseStringBodyFuel : Nat -> AsciiString -> Nat -> ByteArray -> Option ParsedString
  | 0, _text, _pos, _out => none
  | fuel + 1, text, pos, out =>
      if pos < text.size && isJsonBareStringByte (text.get! pos) then
        parseStringBodyFuel fuel text (pos + 1) (out.push (text.get! pos))
      else
        if pos < text.size && text.get! pos == byteQuote then
          some { pos := pos + 1, value := AsciiString.ofTrustedByteArray out }
        else
          none

def parseStringAt (text : AsciiString) (pos : Nat) : Option ParsedString :=
  match expectByte text pos byteQuote with
  | none => none
  | some bodyPos => parseStringBodyFuel (text.size + 1) text bodyPos ByteArray.empty

def skipStringAt (text : AsciiString) (pos : Nat) : Option Nat :=
  match parseStringAt text pos with
  | some parsed => some parsed.pos
  | none => none

def compositeScanContinue (state : CompositeScanState) : Bool :=
  !state.failed && !(state.depth == 0)

def compositeScanStep (text : AsciiString) (state : CompositeScanState) : CompositeScanState :=
  if state.pos < text.size then
    let byte := text.get! state.pos
    if byte == byteQuote then
      match skipStringAt text state.pos with
      | some next => { state with pos := next }
      | none => { state with failed := true }
    else if byte == byteLBrace then
      { state with pos := state.pos + 1, depth := state.depth + 1 }
    else if byte == byteLBracket then
      { state with pos := state.pos + 1, depth := state.depth + 1 }
    else if byte == byteRBrace || byte == byteRBracket then
      if state.depth == 0 then
        { state with failed := true }
      else
        { state with pos := state.pos + 1, depth := state.depth - 1 }
    else
      { state with pos := state.pos + 1 }
  else
    { state with failed := true }

def scanCompositeFuel : Nat -> AsciiString -> CompositeScanState -> CompositeScanState
  | 0, _text, state => state
  | fuel + 1, text, state =>
      if compositeScanContinue state then
        scanCompositeFuel fuel text (compositeScanStep text state)
      else
        state

def skipCompositeAt (text : AsciiString) (pos : Nat) : Option Nat :=
  let state :=
    scanCompositeFuel (text.size + 1) text
      { pos := pos + 1, depth := 1, failed := false }
  if !state.failed && state.depth == 0 then
    some state.pos
  else
    none

def skipValueAt (text : AsciiString) (pos : Nat) : Option Nat :=
  let start := skipWs text pos
  let byte := text.getD start 0
  if byte == byteQuote then
    skipStringAt text start
  else if byte == byteLBrace then
    skipCompositeAt text start
  else if byte == byteLBracket then
    skipCompositeAt text start
  else if isDigit byte then
    match parseUInt64 text start with
    | some parsed => some parsed.pos
    | none => none
  else if byte == byteT then
    expectBytes text start literalTrue
  else if byte == byteF then
    expectBytes text start literalFalse
  else if byte == byteN then
    expectBytes text start literalNull
  else
    none

def arrayRangeScanContinue (state : ArrayRangeState) : Bool :=
  !state.done && !state.failed

def arrayRangeScanStep (text : AsciiString) (state : ArrayRangeState) : ArrayRangeState :=
  let pos0 := skipWs text state.pos
  if pos0 < text.size && text.get! pos0 == byteRBracket then
    if state.canEnd then
      { state with pos := pos0 + 1, done := true }
    else
      { state with failed := true }
  else
    let valueStart := pos0
    match skipValueAt text valueStart with
    | none => { state with failed := true }
    | some valueStop =>
        let ranges := state.ranges.push { start := valueStart, stop := valueStop }
        let afterValue := skipWs text valueStop
        if afterValue < text.size && text.get! afterValue == byteComma then
          { state with pos := afterValue + 1, canEnd := false, ranges := ranges }
        else if afterValue < text.size && text.get! afterValue == byteRBracket then
          { state with pos := afterValue + 1, canEnd := true, done := true, ranges := ranges }
        else
          { state with failed := true }

def arrayRangeScanFuel : Nat -> AsciiString -> ArrayRangeState -> ArrayRangeState
  | 0, _text, state => state
  | fuel + 1, text, state =>
      if arrayRangeScanContinue state then
        arrayRangeScanFuel fuel text (arrayRangeScanStep text state)
      else
        state

def parseArrayRanges (text : AsciiString) : Option (Array FieldRange) :=
  match expectWsByte text 0 byteLBracket with
  | none => none
  | some pos =>
      let state :=
        arrayRangeScanFuel (text.size + 1) text
          { pos := pos, canEnd := true, done := false, failed := false, ranges := #[] }
      if !state.failed && state.done && skipWs text state.pos == text.size then
        some state.ranges
      else
        none

def nameMatchesAt (text : AsciiString) (start stop : Nat) (name : ByteArray) : Bool :=
  match expectBytes text start name with
  | some afterName => afterName + 1 == stop
  | none => false

def fieldSearchContinue (state : FieldSearchState) : Bool :=
  !state.done && !state.failed

def fieldSearchStep (text : AsciiString) (name : ByteArray) (state : FieldSearchState) :
    FieldSearchState :=
  let pos0 := skipWs text state.pos
  if pos0 < text.size && text.get! pos0 == byteRBrace then
    { state with pos := pos0 + 1, done := true }
  else
    match expectByte text pos0 byteQuote with
    | none => { state with failed := true }
    | some nameStart =>
        match skipStringAt text pos0 with
        | none => { state with failed := true }
        | some nameStop =>
            match expectWsByte text nameStop byteColon with
            | none => { state with failed := true }
            | some afterColon =>
                let valueStart := skipWs text afterColon
                match skipValueAt text valueStart with
                | none => { state with failed := true }
                | some valueStop =>
                    let nextState :=
                      if !state.found && nameMatchesAt text nameStart nameStop name then
                        { state with found := true, start := valueStart, stop := valueStop }
                      else
                        state
                    let afterValue := skipWs text valueStop
                    if afterValue < text.size && text.get! afterValue == byteComma then
                      { nextState with pos := afterValue + 1 }
                    else if afterValue < text.size && text.get! afterValue == byteRBrace then
                      { nextState with pos := afterValue + 1, done := true }
                    else
                      { nextState with failed := true }

def fieldSearchFuel : Nat -> AsciiString -> ByteArray -> FieldSearchState -> FieldSearchState
  | 0, _text, _name, state => state
  | fuel + 1, text, name, state =>
      if fieldSearchContinue state then
        fieldSearchFuel fuel text name (fieldSearchStep text name state)
      else
        state

def findFieldRange (text : AsciiString) (name : ByteArray) : Option FieldRange :=
  match expectWsByte text 0 byteLBrace with
  | none => none
  | some pos =>
      let state :=
        fieldSearchFuel (text.size + 1) text name
          { pos := pos, done := false, failed := false, found := false, start := 0, stop := 0 }
      if !state.failed && state.found && skipWs text state.pos == text.size then
        some { start := state.start, stop := state.stop }
      else
        none

def rangeText (text : AsciiString) (range : FieldRange) : AsciiString :=
  text.extract range.start range.stop

def getRawField (text : AsciiString) (name : ByteArray) : Option AsciiString :=
  match findFieldRange text name with
  | some range => some (rangeText text range)
  | none => none

def parseUInt64Range (text : AsciiString) (range : FieldRange) : Option UInt64 :=
  match parseUInt64 text range.start with
  | some parsed =>
      if parsed.pos == range.stop then
        some parsed.value
      else
        none
  | none => none

def getUInt64Field (text : AsciiString) (name : ByteArray) : Option UInt64 :=
  match findFieldRange text name with
  | some range => parseUInt64Range text range
  | none => none

def getStringField (text : AsciiString) (name : ByteArray) : Option AsciiString :=
  match findFieldRange text name with
  | none => none
  | some range =>
      match parseStringAt text range.start with
      | some parsed =>
          if parsed.pos == range.stop then
            some parsed.value
          else
            none
      | none => none

def getBoolField (text : AsciiString) (name : ByteArray) : Option Bool :=
  match findFieldRange text name with
  | none => none
  | some range =>
      match expectBytes text range.start literalTrue with
      | some pos =>
          if pos == range.stop then
            some true
          else
            none
      | none =>
          match expectBytes text range.start literalFalse with
          | some pos =>
              if pos == range.stop then
                some false
              else
                none
          | none => none

def getNullField (text : AsciiString) (name : ByteArray) : Bool :=
  match findFieldRange text name with
  | none => false
  | some range =>
      match expectBytes text range.start literalNull with
      | some pos => pos == range.stop
      | none => false

def getObjectField (text : AsciiString) (name : ByteArray) : Option AsciiString :=
  match findFieldRange text name with
  | some range =>
      if text.getD range.start 0 == byteLBrace then
        some (rangeText text range)
      else
        none
  | none => none

def getArrayField (text : AsciiString) (name : ByteArray) : Option AsciiString :=
  match findFieldRange text name with
  | some range =>
      if text.getD range.start 0 == byteLBracket then
        some (rangeText text range)
      else
        none
  | none => none

def getArrayRangesField (text : AsciiString) (name : ByteArray) :
    Option (Array FieldRange) :=
  match getArrayField text name with
  | some arrayText => parseArrayRanges arrayText
  | none => none

def appendQuotedBytesFuel : Nat -> ByteArray -> Nat -> ByteArray -> Option ByteArray
  | 0, _bytes, _index, _out => none
  | fuel + 1, bytes, index, out =>
      if index < bytes.size && isJsonBareStringByte (bytes.get! index) then
        appendQuotedBytesFuel fuel bytes (index + 1) (out.push (bytes.get! index))
      else
        if index == bytes.size then
          some (out.push byteQuote)
        else
          none

def appendQuotedBytes? (out bytes : ByteArray) : Option ByteArray :=
  appendQuotedBytesFuel (bytes.size + 1) bytes 0 (out.push byteQuote)

def appendQuotedString? (out : ByteArray) (text : AsciiString) : Option ByteArray :=
  appendQuotedBytes? out text.toByteArray

def appendFieldPrefix? (out : ByteArray) (first : Bool) (name : ByteArray) : Option ByteArray :=
  let out1 := if first then out else out.push byteComma
  match appendQuotedBytes? out1 name with
  | some out2 => some (out2.push byteColon)
  | none => none

def appendUInt64Field? (out : ByteArray) (first : Bool) (name : ByteArray) (value : UInt64) :
    Option ByteArray :=
  match appendFieldPrefix? out first name with
  | some out1 => some (appendUInt64Decimal out1 value)
  | none => none

def appendBoolField? (out : ByteArray) (first : Bool) (name : ByteArray) (value : Bool) :
    Option ByteArray :=
  match appendFieldPrefix? out first name with
  | some out1 =>
      if value then
        some (out1.append literalTrue)
      else
        some (out1.append literalFalse)
  | none => none

def appendNullField? (out : ByteArray) (first : Bool) (name : ByteArray) : Option ByteArray :=
  match appendFieldPrefix? out first name with
  | some out1 => some (out1.append literalNull)
  | none => none

def appendStringField? (out : ByteArray) (first : Bool) (name : ByteArray) (value : AsciiString) :
    Option ByteArray :=
  match appendFieldPrefix? out first name with
  | some out1 => appendQuotedString? out1 value
  | none => none

def rawValueIsComplete (value : AsciiString) : Bool :=
  match skipValueAt value 0 with
  | some pos => skipWs value pos == value.size
  | none => false

def appendRawField? (out : ByteArray) (first : Bool) (name : ByteArray) (value : AsciiString) :
    Option ByteArray :=
  if rawValueIsComplete value then
    match appendFieldPrefix? out first name with
    | some out1 => some (out1.append value.toByteArray)
    | none => none
  else
    none

def object1UInt64 (name : ByteArray) (value : UInt64) : ByteArray :=
  match appendUInt64Field? (ByteArray.empty.push byteLBrace) true name value with
  | some out => out.push byteRBrace
  | none => errorJson

def object1Bool (name : ByteArray) (value : Bool) : ByteArray :=
  match appendBoolField? (ByteArray.empty.push byteLBrace) true name value with
  | some out => out.push byteRBrace
  | none => errorJson

def object1String (name : ByteArray) (value : AsciiString) : ByteArray :=
  match appendStringField? (ByteArray.empty.push byteLBrace) true name value with
  | some out => out.push byteRBrace
  | none => errorJson

end Json
end Ascii
end LeanExe
