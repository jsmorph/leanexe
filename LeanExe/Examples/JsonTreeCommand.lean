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

def buildTreeFuel : Nat -> Array Ascii.Json.Value -> Nat -> BuildState -> BuildState
  | 0, _items, _index, state => { state with failed := true }
  | fuel + 1, items, index, state =>
      if state.failed || index == items.size then
        state
      else
        buildTreeFuel fuel items (index + 1) (addJsonValue state items[index]!)

def buildTree : Ascii.Json.Value -> Option Tree
  | Ascii.Json.Value.null => none
  | Ascii.Json.Value.bool _ => none
  | Ascii.Json.Value.num _ => none
  | Ascii.Json.Value.str _ => none
  | Ascii.Json.Value.arr items =>
      let state :=
        buildTreeFuel (items.size + 1) items 0
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

def containsJsonTreeFuel : Nat -> Ascii.Json.Value -> UInt64 -> Option Bool
  | 0, _tree, _needle => none
  | fuel + 1, tree, needle =>
      match tree with
      | Ascii.Json.Value.null => some false
      | Ascii.Json.Value.obj _fields =>
          match Ascii.Json.get? tree valueFieldName with
          | none => none
          | some valueJson =>
              match Ascii.Json.asUInt64? valueJson with
              | none => none
              | some value =>
                  if needle == value then
                    some true
                  else if needle < value then
                    match Ascii.Json.get? tree leftFieldName with
                    | some leftTree => containsJsonTreeFuel fuel leftTree needle
                    | none => none
                  else
                    match Ascii.Json.get? tree rightFieldName with
                    | some rightTree => containsJsonTreeFuel fuel rightTree needle
                    | none => none
      | Ascii.Json.Value.bool _ => none
      | Ascii.Json.Value.num _ => none
      | Ascii.Json.Value.str _ => none
      | Ascii.Json.Value.arr _ => none

def containsJsonTree? (tree : Ascii.Json.Value) (fuel : Nat) (needle : UInt64) : Option Bool :=
  containsJsonTreeFuel fuel tree needle

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

def searchTreeValue (tree : Ascii.Json.Value) (args : Array ByteArray) (fuel : Nat) :
    Except ByteArray ByteArray :=
  match parseNeedle args with
  | none => Except.error Ascii.Json.errorJson
  | some needle =>
      match containsJsonTree? tree fuel needle with
      | some found =>
          Except.ok (Ascii.Json.render (Ascii.Json.object1Value foundFieldName (Ascii.Json.Value.bool found)))
      | none => Except.error Ascii.Json.errorJson

def searchTree (input : ByteArray) (args : Array ByteArray) : Except ByteArray ByteArray :=
  match Ascii.Json.parseBytes input with
  | some tree => searchTreeValue tree args (input.size + 1)
  | none => Except.error Ascii.Json.errorJson

end Examples.JsonTreeCommand
end LeanExe
