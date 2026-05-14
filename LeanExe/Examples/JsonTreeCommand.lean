import LeanExe.Ascii.Json.Value

namespace LeanExe
namespace Examples.JsonTreeCommand

inductive Tree where
  | empty : Tree
  | node : UInt64 -> Tree -> Tree -> Tree

def fieldName (bytes : ByteArray) : AsciiString :=
  AsciiString.ofTrustedByteArray bytes

def valueFieldBytes : ByteArray :=
  "value".toUTF8

def leftFieldBytes : ByteArray :=
  "left".toUTF8

def rightFieldBytes : ByteArray :=
  "right".toUTF8

def foundFieldBytes : ByteArray :=
  "found".toUTF8

def valueFieldName : AsciiString :=
  fieldName valueFieldBytes

def leftFieldName : AsciiString :=
  fieldName leftFieldBytes

def rightFieldName : AsciiString :=
  fieldName rightFieldBytes

def foundFieldName : AsciiString :=
  fieldName foundFieldBytes

structure BuildState where
  failed : Bool
  tree : Tree

structure DecodeState where
  failed : Bool
  seenValue : Bool
  value : UInt64
  seenLeft : Bool
  left : Tree
  seenRight : Bool
  right : Tree

def DecodeState.fail (state : DecodeState) : DecodeState :=
  { state with failed := true }

def initialDecodeState : DecodeState :=
  {
    failed := false,
    seenValue := false,
    value := 0,
    seenLeft := false,
    left := Tree.empty,
    seenRight := false,
    right := Tree.empty
  }

def insert (tree : Tree) (value : UInt64) : Tree :=
  match tree with
  | Tree.empty => Tree.node value Tree.empty Tree.empty
  | Tree.node current left right =>
      if value < current then
        Tree.node current (insert left value) right
      else
        Tree.node current left (insert right value)

def addJsonValue (state : BuildState) (value : Ascii.Json.Value) : BuildState :=
  if state.failed then
    state
  else
    match Ascii.Json.asUInt64? value with
    | some value => { failed := false, tree := insert state.tree value }
    | none => { state with failed := true }

def buildTree : Ascii.Json.Value -> Option Tree
  | Ascii.Json.Value.null => none
  | Ascii.Json.Value.bool _ => none
  | Ascii.Json.Value.num _ => none
  | Ascii.Json.Value.str _ => none
  | Ascii.Json.Value.arr items =>
      let state :=
        items.foldl (fun state value => addJsonValue state value)
          { failed := false, tree := Tree.empty }
      if state.failed then
        none
      else
        some state.tree
  | Ascii.Json.Value.obj _ => none

def treeJson? : Tree -> Option ByteArray
  | Tree.empty => some Ascii.Json.literalNull
  | Tree.node value left right =>
      match treeJson? left with
      | none => none
      | some leftJson =>
          match treeJson? right with
          | none => none
          | some rightJson =>
              match Ascii.Json.appendUInt64Field?
                  (ByteArray.empty.push Ascii.byteLBrace) true valueFieldBytes value with
              | none => none
              | some out1 =>
                  match Ascii.Json.appendRawField? out1 false leftFieldBytes
                      (AsciiString.ofTrustedByteArray leftJson) with
                  | none => none
                  | some out2 =>
                      match Ascii.Json.appendRawField? out2 false rightFieldBytes
                          (AsciiString.ofTrustedByteArray rightJson) with
                      | none => none
                      | some out3 => some (out3.push Ascii.byteRBrace)

def makeTreeValue (value : Ascii.Json.Value) : Except ByteArray ByteArray :=
  match buildTree value with
  | some tree =>
      match treeJson? tree with
      | some bytes => Except.ok bytes
      | none => Except.error Ascii.Json.errorJson
  | none => Except.error Ascii.Json.errorJson

def makeTree (input : ByteArray) : Except ByteArray ByteArray :=
  match Ascii.Json.parseBytes input with
  | some value => makeTreeValue value
  | none => Except.error Ascii.Json.errorJson

def decodeTree : Ascii.Json.Value -> Option Tree
  | Ascii.Json.Value.null => some Tree.empty
  | Ascii.Json.Value.obj fields =>
      let state :=
        fields.attach.foldl
          (fun state item =>
            match item with
            | ⟨field, _hmem⟩ =>
                let name := Ascii.Json.Field.name field
                let value := Ascii.Json.Field.value field
                if state.failed then
                  state
                else if name.equals valueFieldName then
                  if state.seenValue then
                    DecodeState.fail state
                  else
                    match Ascii.Json.asUInt64? value with
                    | some value => { state with seenValue := true, value := value }
                    | none => DecodeState.fail state
                else if name.equals leftFieldName then
                  if state.seenLeft then
                    DecodeState.fail state
                  else
                    match decodeTree value with
                    | some left => { state with seenLeft := true, left := left }
                    | none => DecodeState.fail state
                else if name.equals rightFieldName then
                  if state.seenRight then
                    DecodeState.fail state
                  else
                    match decodeTree value with
                    | some right => { state with seenRight := true, right := right }
                    | none => DecodeState.fail state
                else
                  DecodeState.fail state)
          initialDecodeState
      if state.failed || !state.seenValue || !state.seenLeft || !state.seenRight then
        none
      else
        some (Tree.node state.value state.left state.right)
  | Ascii.Json.Value.bool _ => none
  | Ascii.Json.Value.num _ => none
  | Ascii.Json.Value.str _ => none
  | Ascii.Json.Value.arr _ => none
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    have hField : sizeOf field < sizeOf fields :=
      Array.sizeOf_lt_of_mem _hmem
    cases field with
    | mk name value =>
        simp [Ascii.Json.Field.value] at hField ⊢
        omega

def contains (tree : Tree) (needle : UInt64) : Bool :=
  match tree with
  | Tree.empty => false
  | Tree.node value left right =>
      if needle == value then
        true
      else if needle < value then
        contains left needle
      else
        contains right needle

def parseUInt64Text (text : AsciiString) : Option UInt64 :=
  let pos := Ascii.skipWs text 0
  match Ascii.parseUInt64 text pos with
  | some parsed =>
      if Ascii.skipWs text parsed.pos == text.size then
        some parsed.value
      else
        none
  | none => none

def parseNeedle (args : Array ByteArray) : Option UInt64 :=
  if args.size == 1 then
    match AsciiString.ofByteArray? args[0]! with
    | some text => parseUInt64Text text
    | none => none
  else
    none

def searchTreeValue (tree : Tree) (args : Array ByteArray) : Except ByteArray ByteArray :=
  match parseNeedle args with
  | none => Except.error Ascii.Json.errorJson
  | some needle =>
      Except.ok
        (Ascii.Json.render
          (Ascii.Json.object1Value foundFieldName (Ascii.Json.Value.bool (contains tree needle))))

def searchTree (input : ByteArray) (args : Array ByteArray) : Except ByteArray ByteArray :=
  match Ascii.Json.parseBytes input with
  | some value =>
      match decodeTree value with
      | some tree => searchTreeValue tree args
      | none => Except.error Ascii.Json.errorJson
  | none => Except.error Ascii.Json.errorJson

end Examples.JsonTreeCommand
end LeanExe
