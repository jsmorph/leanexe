import LeanExe.Packed
import LeanExe.Runtime

namespace LeanExe.Examples.HeapLoops

structure Buffers where
  status : UInt64
  hidden : ByteArray
  update : ByteArray

def step (input : ByteArray) (index stop : Nat) : Buffers :=
  if index == stop then { status := 1, hidden := .empty, update := .empty }
  else { status := 0, hidden := input.push (UInt8.ofNat index), update := ByteArray.empty.push 99 }

def conditional (count stop : Nat) : ByteArray := Id.run do
  let mut hidden := ByteArray.empty.push 42
  let mut updates := ByteArray.empty
  let mut status : UInt64 := 0
  for index in [:count] do
    if status == 0 then
      let result := step hidden index stop
      status := result.status
      hidden := result.hidden
      updates := updates ++ result.update
  return hidden ++ updates

def initialAlias (count skip : Nat) : UInt64 := Id.run do
  let initial := ByteArray.empty.push 42
  let mut value := initial
  for index in [:count] do
    if index >= skip then value := value.push (UInt8.ofNat index)
  return initial[0]!.toUInt64 + UInt64.ofNat value.size

def crossField (count skip : Nat) : UInt64 := Id.run do
  let first := ByteArray.empty.push 42
  let second := ByteArray.empty.push 43
  let mut left := first
  let mut right := second
  for index in [:count] do
    let next := if index >= skip then right.push (UInt8.ofNat index) else right
    right := left
    left := next
  return first[0]!.toUInt64 + second[0]!.toUInt64 + left[0]!.toUInt64 + right[0]!.toUInt64 +
    UInt64.ofNat (left.size + right.size)

def freshArray (input : Array UInt64) : Array UInt64 := input.map (fun value => value + 1)

def conditionalFold (input initial : Array UInt64) : Array UInt64 :=
  input.foldl (fun output value => if value == 0 then output else output.push value) initial

def releaseAlias (replace : Nat) (input : Array UInt64) : Array UInt64 :=
  let first := freshArray input
  if replace == 1 then
    let result := freshArray first
    let _ := Runtime.release first
    result
  else first

end LeanExe.Examples.HeapLoops
