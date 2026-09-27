import LeanExe.Examples.JsonTreeCommand
import LeanExe.Runtime

namespace LeanExe
namespace Examples.JsonGcTreeRewrite

open Ascii.Json
open Examples.JsonTreeCommand

structure Config where
  depth : UInt64
  rounds : UInt64
  salt : UInt64
  search : UInt64

structure RunState where
  tree : Tree
  checksum : UInt64
  lastFree : UInt64

structure Metrics where
  found : Bool
  nodeCount : UInt64
  height : UInt64
  checksum : UInt64
  allocsAfterInitial : UInt64
  freesBeforeRun : UInt64
  freesAfterRounds : UInt64
  releasesAfterFinal : UInt64
  freesAfterFinal : UInt64

def depthFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "depth".toUTF8

def roundsFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "rounds".toUTF8

def saltFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "salt".toUTF8

def searchFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "search".toUTF8

def nodeCountFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "nodeCount".toUTF8

def heightFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "height".toUTF8

def checksumFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "checksum".toUTF8

def gcFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "gc".toUTF8

def allocsAfterInitialFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "allocsAfterInitial".toUTF8

def freesBeforeRunFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "freesBeforeRun".toUTF8

def freesAfterRoundsFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "freesAfterRounds".toUTF8

def releasesAfterFinalFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "releasesAfterFinal".toUTF8

def freesAfterFinalFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "freesAfterFinal".toUTF8

def maxDepth : UInt64 :=
  8

def maxRounds : UInt64 :=
  40

def valueModulus : UInt64 :=
  1000003

def nextSeed (seed salt round step : UInt64) : UInt64 :=
  seed * 2862933555777941757 + 3037000493 + salt + round * 97 + step

def generatedValue (seed : UInt64) : UInt64 :=
  seed % valueModulus

def transformValue (value round salt : UInt64) : UInt64 :=
  (value * 1103515245 + round * 12345 + salt * 97 + 17) % valueModulus

def buildTreeFuel : Nat -> UInt64 -> UInt64 -> Tree
  | 0, _salt, _seed => Tree.empty
  | fuel + 1, salt, seed =>
      let level := Nat.toUInt64 fuel
      let valueSeed := nextSeed seed salt level 0
      let leftSeed := nextSeed seed salt level 1
      let rightSeed := nextSeed seed salt level 2
      Tree.node (generatedValue valueSeed)
        (buildTreeFuel fuel salt leftSeed)
        (buildTreeFuel fuel salt rightSeed)

def buildInitialTree (depth salt : UInt64) : Tree :=
  buildTreeFuel depth.toNat salt (salt + 1)

def rewriteTree : Tree -> UInt64 -> UInt64 -> Tree
  | Tree.empty, _round, _salt => Tree.empty
  | Tree.node value left right, round, salt =>
      let transformed := transformValue value round salt
      Tree.node transformed
        (rewriteTree left round salt)
        (rewriteTree right round salt)

def treeChecksum : Tree -> UInt64
  | Tree.empty => 0
  | Tree.node value left right => value + treeChecksum left + treeChecksum right

def containsAny : Tree -> UInt64 -> Bool
  | Tree.empty, _needle => false
  | Tree.node value left right, needle =>
      if value == needle then
        true
      else if containsAny left needle then
        true
      else
        containsAny right needle

def runRoundsFuel : Nat -> UInt64 -> UInt64 -> RunState -> RunState
  | 0, _round, _salt, state => state
  | fuel + 1, round, salt, state =>
      let rewritten := rewriteTree state.tree round salt
      let checksum := treeChecksum rewritten
      let freeAfter := Runtime.release state.tree
      runRoundsFuel fuel (round + 1) salt
        {
          tree := rewritten,
          checksum := state.checksum + checksum,
          lastFree := freeAfter
        }

def runRounds (tree : Tree) (rounds salt initialChecksum : UInt64) : RunState :=
  runRoundsFuel rounds.toNat 1 salt
    { tree := tree, checksum := initialChecksum, lastFree := Runtime.freeCount }

def treeSize : Tree -> UInt64
  | Tree.empty => 0
  | Tree.node _ left right => 1 + treeSize left + treeSize right

def treeHeight : Tree -> UInt64
  | Tree.empty => 0
  | Tree.node _ left right => 1 + max (treeHeight left) (treeHeight right)

def uint64Field? (value : Value) (name : AsciiString) : Option UInt64 :=
  match get? value name with
  | some fieldValue => asUInt64? fieldValue
  | none => none

def validConfig (config : Config) : Bool :=
  config.depth != 0 &&
    config.depth <= maxDepth &&
    config.rounds <= maxRounds

def parseConfig (value : Value) : Option Config :=
  match uint64Field? value depthFieldName with
  | some depth =>
      match uint64Field? value roundsFieldName with
      | some rounds =>
          match uint64Field? value saltFieldName with
          | some salt =>
              match uint64Field? value searchFieldName with
              | some search =>
                  let config := { depth := depth, rounds := rounds, salt := salt, search := search }
                  if validConfig config then
                    some config
                  else
                    none
              | none => none
          | none => none
      | none => none
  | none => none

def gcValue (metrics : Metrics) : Value :=
  Value.obj #[
    Field.mk allocsAfterInitialFieldName (Value.num metrics.allocsAfterInitial),
    Field.mk freesBeforeRunFieldName (Value.num metrics.freesBeforeRun),
    Field.mk freesAfterRoundsFieldName (Value.num metrics.freesAfterRounds),
    Field.mk releasesAfterFinalFieldName (Value.num metrics.releasesAfterFinal),
    Field.mk freesAfterFinalFieldName (Value.num metrics.freesAfterFinal)
  ]

def metricsValue (metrics : Metrics) : Value :=
  Value.obj #[
    Field.mk foundFieldName (Value.bool metrics.found),
    Field.mk nodeCountFieldName (Value.num metrics.nodeCount),
    Field.mk heightFieldName (Value.num metrics.height),
    Field.mk checksumFieldName (Value.num metrics.checksum),
    Field.mk gcFieldName (gcValue metrics)
  ]

def runConfig (config : Config) : Except ByteArray ByteArray :=
  let initial := buildInitialTree config.depth config.salt
  let initialChecksum := treeChecksum initial
  let allocsAfterInitial := Runtime.allocCount
  let freesBeforeRun := Runtime.freeCount
  let finalState := runRounds initial config.rounds config.salt initialChecksum
  let found := containsAny finalState.tree config.search
  let nodeCount := treeSize finalState.tree
  let height := treeHeight finalState.tree
  let freesAfterRounds := finalState.lastFree
  let freesAfterFinal := Runtime.release finalState.tree
  let releasesAfterFinal := Runtime.releaseCount
  let metrics :=
    {
      found := found,
      nodeCount := nodeCount,
      height := height,
      checksum := finalState.checksum,
      allocsAfterInitial := allocsAfterInitial,
      freesBeforeRun := freesBeforeRun,
      freesAfterRounds := freesAfterRounds,
      releasesAfterFinal := releasesAfterFinal,
      freesAfterFinal := freesAfterFinal
    }
  match render? (metricsValue metrics) with
  | some bytes => Except.ok bytes
  | none => Except.error errorJson

def transform (input : ByteArray) : Except ByteArray ByteArray :=
  match parseBytes input with
  | some value =>
      match parseConfig value with
      | some config => runConfig config
      | none => Except.error errorJson
  | none => Except.error errorJson

end Examples.JsonGcTreeRewrite
end LeanExe
