import LeanExe.Examples.JsonTreeCommand
import LeanExe.Runtime

namespace LeanExe
namespace Examples.JsonMergeTreeCommand

open Ascii.Json
open Examples.JsonTreeCommand

def treeFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "tree".toUTF8

def gcFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "gc".toUTF8

def allocsFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "allocs".toUTF8

def releasesBeforeFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "releasesBefore".toUTF8

def freesBeforeFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "freesBefore".toUTF8

def freesAfterFirstFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "freesAfterFirst".toUTF8

def freesAfterSecondFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "freesAfterSecond".toUTF8

def releasesAfterSecondFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "releasesAfterSecond".toUTF8

def releasesFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "releases".toUTF8

def freesFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "frees".toUTF8

def mergeInto : Tree -> Tree -> Tree
  | Tree.empty, acc => acc
  | Tree.node value left right, acc =>
      let withLeft := mergeInto left acc
      let withValue := insert withLeft value
      mergeInto right withValue

def mergeTrees (first second : Tree) : Tree :=
  let withFirst := mergeInto first Tree.empty
  mergeInto second withFirst

def gcValue
    (allocs releasesBefore freesBefore freesAfterFirst freesAfterSecond
      releasesAfterSecond : UInt64) :
    Value :=
  Value.obj #[
    Field.mk allocsFieldName (Value.num allocs),
    Field.mk releasesBeforeFieldName (Value.num releasesBefore),
    Field.mk freesBeforeFieldName (Value.num freesBefore),
    Field.mk freesAfterFirstFieldName (Value.num freesAfterFirst),
    Field.mk freesAfterSecondFieldName (Value.num freesAfterSecond),
    Field.mk releasesAfterSecondFieldName (Value.num releasesAfterSecond)
  ]

def mergedTreeValue
    (tree : Tree)
    (allocs releasesBefore freesBefore freesAfterFirst freesAfterSecond
      releasesAfterSecond : UInt64) :
    Value :=
  Value.obj #[
    Field.mk treeFieldName (treeValue tree),
    Field.mk gcFieldName
      (gcValue allocs releasesBefore freesBefore freesAfterFirst freesAfterSecond
        releasesAfterSecond)
  ]

def makeMergedTreeValue : Value -> Except ByteArray ByteArray
  | Value.arr items =>
      if items.size == 2 then
        match buildTree items[0]! with
        | some first =>
            match buildTree items[1]! with
            | some second =>
                let merged := mergeTrees first second
                let allocs := Runtime.allocCount
                let releasesBefore := Runtime.releaseCount
                let freesBefore := Runtime.freeCount
                let freesAfterFirst := Runtime.release first
                let freesAfterSecond := Runtime.release second
                let releasesAfterSecond := Runtime.releaseCount
                match render?
                    (mergedTreeValue merged allocs releasesBefore freesBefore freesAfterFirst
                      freesAfterSecond releasesAfterSecond) with
                | some bytes => Except.ok bytes
                | none => Except.error errorJson
            | none => Except.error errorJson
        | none => Except.error errorJson
      else
        Except.error errorJson
  | Value.null => Except.error errorJson
  | Value.bool _ => Except.error errorJson
  | Value.num _ => Except.error errorJson
  | Value.str _ => Except.error errorJson
  | Value.obj _ => Except.error errorJson

def makeMergedTree (input : ByteArray) : Except ByteArray ByteArray :=
  match parseBytes input with
  | some value => makeMergedTreeValue value
  | none => Except.error errorJson

def decodeMergedTreeInput (value : Value) : Option Tree :=
  match get? value treeFieldName with
  | some treeJson => decodeTree treeJson
  | none => none

def searchResultValue (found : Bool) : Value :=
  Value.obj #[
    Field.mk foundFieldName (Value.bool found),
    Field.mk allocsFieldName (Value.num Runtime.allocCount),
    Field.mk releasesFieldName (Value.num Runtime.releaseCount),
    Field.mk freesFieldName (Value.num Runtime.freeCount)
  ]

def searchMergedTreeValue (tree : Tree) (args : Array ByteArray) : Except ByteArray ByteArray :=
  match parseNeedle args with
  | none => Except.error errorJson
  | some needle =>
      match render? (searchResultValue (contains tree needle)) with
      | some bytes => Except.ok bytes
      | none => Except.error errorJson

def searchMergedTree (input : ByteArray) (args : Array ByteArray) : Except ByteArray ByteArray :=
  match parseBytes input with
  | some value =>
      match decodeMergedTreeInput value with
      | some tree => searchMergedTreeValue tree args
      | none => Except.error errorJson
  | none => Except.error errorJson

end Examples.JsonMergeTreeCommand
end LeanExe
