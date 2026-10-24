import Verified.Wasi.ReflectProgram
import LeanExe.Encoding.RoundTrip

namespace Verified.Wasi.ReflectProgramCases

open Lean Meta
open LeanExe LeanExe.Wasi LeanExe.Pipeline

def table : Array UInt64 := #[11, 23, 37]

def lookup (values : Array UInt64) (index : UInt64) : UInt64 := values[index.toNat]!

def boundLookup (index : UInt64) : UInt64 := lookup table index

def pureByte (index : UInt64) : UInt64 := (bytes![9, 8]).get index

def helper (index : UInt64) : Action UInt64 := pure (boundLookup index + pureByte 1)

def caller (index : UInt64) : Action UInt64 := do
  let read ← readSome 1
  let value ← helper (index + read.bytes.get 0)
  let write ← writeStdoutSome bytes![65, 0, 255]
  pure (value + write.count)

def main : Action UInt64 := caller 0

def borrowBytes (bytes : LeanExe.Bytes) : Action UInt64 := pure bytes.size

def ownBytes (bytes : LeanExe.Bytes) : Action LeanExe.Bytes := pure bytes

structure Packet where
  count : UInt64
  bytes : LeanExe.Bytes

instance : Flat Packet (UInt64 × LeanExe.Bytes) := ⟨fun packet => (packet.count, packet.bytes)⟩

def packetHelper (packet : Packet) : Action UInt64 := do
  let write ← writeStdoutSome packet.bytes
  pure (packet.count + write.count)

def argumentCaller : Action UInt64 := do
  let read ← readSome 2
  let size ← borrowBytes read.bytes
  let bytes ← ownBytes read.bytes
  let computed ← borrowBytes (LeanExe.Bytes.build 2 fun index => 65 + index)
  let packet ← packetHelper (Packet.mk size bytes)
  pure (size + computed + packet)

run_elab do
  let mut pureState : Verified.Reflect.ProgramReflection := {}
  for name in [``lookup, ``boundLookup, ``pureByte] do
    pureState ← Verified.Reflect.reflectProgramFunction
      `Verified.Wasi.ReflectProgramCases.pureSources name pureState
  let mut state := Reflect.ProgramReflection.empty pureState
  for name in [``helper, ``caller, ``main, ``borrowBytes, ``ownBytes, ``packetHelper, ``argumentCaller] do
    state ← Reflect.reflectProgramFunction `Verified.Wasi.ReflectProgramCases.effects name state
  discard (Reflect.materializeProgram `Verified.Wasi.ReflectProgramCases.callable state
    [``helper, ``caller, ``argumentCaller])
  discard (Reflect.materializeProgram `Verified.Wasi.ReflectProgramCases.command state [] (some ``main))

#guard effects.helper.func.params = [.array .word, .word]
#guard effects.helper.func.modes = [.borrowed, .borrowed]
#guard effects.main.func.params = [.array .word]
#guard effects.main.func.modes = [.borrowed]
#guard effects.borrowBytes.func.modes = [.borrowed, .borrowed]
#guard effects.ownBytes.func.modes = [.borrowed, .owned]
#guard effects.argumentCaller.func.body.placeArgs
#guard callable.literalPool.base = 4128
#guard callable.literalPool.values = [[9, 8], [65, 0, 255]]
#guard command.literalPool.base = callable.literalPool.base
#guard command.literalPool.values = callable.literalPool.values
#guard callable.module.exports.map Wasm.Export.name = ["alloc", "release", "helper", "caller", "argumentCaller"]
#guard command.module.exports.map Wasm.Export.name = ["_start"]
#guard command.module.globalExports = []

theorem callable_bytes : ∃ bytes, Wasm.Encoding.encode callable.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok callable.module :=
  Wasm.Encoding.round_trip callable.module (by decide +kernel) (by decide +kernel)

theorem command_bytes : ∃ bytes, Wasm.Encoding.encode command.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok command.module :=
  Wasm.Encoding.round_trip command.module (by decide +kernel) (by decide +kernel)

end Verified.Wasi.ReflectProgramCases
