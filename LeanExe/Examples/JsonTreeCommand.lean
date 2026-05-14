import LeanExe.Ascii.Json.Value

namespace LeanExe
namespace Examples.JsonTreeCommand

open Ascii.Json

inductive Tree where
  | empty : Tree
  | node : UInt64 -> Tree -> Tree -> Tree

def valueFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "value".toUTF8

def leftFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "left".toUTF8

def rightFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "right".toUTF8

def foundFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "found".toUTF8

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

def addJsonValue (state : Option Tree) (value : Value) : Option Tree :=
  match state with
  | some tree =>
      match asUInt64? value with
      | some value => some (insert tree value)
      | none => none
  | none => none

def buildTree : Value -> Option Tree
  | Value.null => none
  | Value.bool _ => none
  | Value.num _ => none
  | Value.str _ => none
  | Value.arr items =>
      items.foldl (fun state value => addJsonValue state value) (some Tree.empty)
  | Value.obj _ => none

def treeValue : Tree -> Value
  | Tree.empty => Value.null
  | Tree.node value left right =>
      Value.obj #[
        Field.mk valueFieldName (Value.num value),
        Field.mk leftFieldName (treeValue left),
        Field.mk rightFieldName (treeValue right)
      ]

def makeTreeValue (value : Value) : Except ByteArray ByteArray :=
  match buildTree value with
  | some tree =>
      match render? (treeValue tree) with
      | some bytes => Except.ok bytes
      | none => Except.error errorJson
  | none => Except.error errorJson

def makeTree (input : ByteArray) : Except ByteArray ByteArray :=
  match parseBytes input with
  | some value => makeTreeValue value
  | none => Except.error errorJson

def decodeTree : Value -> Option Tree
  | Value.null => some Tree.empty
  | Value.obj fields =>
      let state :=
        fields.attach.foldl
          (fun state item =>
            match item with
            | ⟨field, _hmem⟩ =>
                let name := Field.name field
                let value := Field.value field
                if state.failed then
                  state
                else if name.equals valueFieldName then
                  if state.seenValue then
                    DecodeState.fail state
                  else
                    match asUInt64? value with
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
  | Value.bool _ => none
  | Value.num _ => none
  | Value.str _ => none
  | Value.arr _ => none
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    have hField : sizeOf field < sizeOf fields :=
      Array.sizeOf_lt_of_mem _hmem
    cases field with
    | mk name value =>
        simp [Field.value] at hField ⊢
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
  | none => Except.error errorJson
  | some needle =>
      Except.ok
        (render (object1Value foundFieldName (Value.bool (contains tree needle))))

def searchTree (input : ByteArray) (args : Array ByteArray) : Except ByteArray ByteArray :=
  match parseBytes input with
  | some value =>
      match decodeTree value with
      | some tree => searchTreeValue tree args
      | none => Except.error errorJson
  | none => Except.error errorJson

end Examples.JsonTreeCommand
end LeanExe
