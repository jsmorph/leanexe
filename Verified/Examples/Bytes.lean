import Verified.Reflect.Command

namespace Verified.Examples.Bytes

def identity (bytes : LeanExe.Bytes) : LeanExe.Bytes := bytes

def duplicate (bytes : LeanExe.Bytes) : LeanExe.Bytes × LeanExe.Bytes := (bytes, bytes)

def choose (condition : Bool) (first second : LeanExe.Bytes) : LeanExe.Bytes :=
  if condition then first else second

def discard (bytes : LeanExe.Bytes) : UInt64 :=
  let _copy := identity bytes
  7

def swap (first second : LeanExe.Bytes) : LeanExe.Bytes × LeanExe.Bytes :=
  let pair := (identity first, identity second)
  (pair.2, pair.1)

def firstDuplicate (bytes : LeanExe.Bytes) : LeanExe.Bytes :=
  let pair := duplicate bytes
  pair.1

def secondDuplicate (bytes : LeanExe.Bytes) : LeanExe.Bytes :=
  let pair := duplicate bytes
  pair.2

def swappedFirst (first second : LeanExe.Bytes) : LeanExe.Bytes :=
  let pair := swap first second
  pair.1

def emptyBuffer : LeanExe.Bytes := LeanExe.Bytes.empty

def readSize (bytes : LeanExe.Bytes) : UInt64 := bytes.size

def readByte (bytes : LeanExe.Bytes) (index : UInt64) : UInt64 := bytes.get index

def ownedSize (bytes : LeanExe.Bytes) : UInt64 := (identity bytes).size

def ownedByte (bytes : LeanExe.Bytes) (index : UInt64) : UInt64 := (identity bytes).get index

def lastByte (bytes : LeanExe.Bytes) : UInt64 :=
  let owned := identity bytes
  owned.get (owned.size - 1)

def emptyRead (index : UInt64) : UInt64 := LeanExe.Bytes.empty.get index

def buildPattern (count start : UInt64) : LeanExe.Bytes :=
  LeanExe.Bytes.build count fun i => start + i * 257

def copyByBuild (bytes : LeanExe.Bytes) : LeanExe.Bytes :=
  LeanExe.Bytes.build bytes.size fun i => bytes.get i

def buildFromOwned (bytes : LeanExe.Bytes) (count : UInt64) : LeanExe.Bytes :=
  let owned := identity bytes
  LeanExe.Bytes.build count fun i => owned.get i

def buildFromSize (bytes : LeanExe.Bytes) : LeanExe.Bytes :=
  let owned := identity bytes
  LeanExe.Bytes.build owned.size fun i => i

def nestedBuild (count : UInt64) : LeanExe.Bytes :=
  LeanExe.Bytes.build count fun i =>
    let owned := LeanExe.Bytes.build 1 fun _ => i + 255
    owned.get 0

verified_compile compiled := [identity, duplicate, choose, discard, swap, firstDuplicate,
  secondDuplicate, swappedFirst, emptyBuffer, readSize, readByte, ownedSize, ownedByte, lastByte,
  emptyRead, buildPattern, copyByBuild, buildFromOwned, buildFromSize, nestedBuild]

end Verified.Examples.Bytes
