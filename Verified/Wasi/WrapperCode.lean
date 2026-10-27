import Verified.Wasi.ABI
import LeanExe.Wasi.Action

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def metadataCode (pointer length : Nat) : Program :=
  [.const 0, .localGet pointer, .wrapI64, .store32 0,
   .const 4, .localGet length, .wrapI64, .store32 0,
   .const 8, .const 0, .store32 0]

def writeCode (output : Output) (pointer length errno : Nat) : Program :=
  metadataCode pointer length ++
    [.const output.fd.toUInt32, .const 0, .const 1, .const 8, .call 1,
     .localSet errno, .localGet errno, .extendUI32,
     .localGet errno, .eqz,
     .iff 0 1 [.const 8, .load32 0, .extendUI32] [.constI64 0] [] [.i64]]

def writeFunction (output : Output) (typeIdx : Nat) : Function :=
  { params := [.i64, .i64]
    locals := [.i32]
    results := [.i64, .i64]
    body := writeCode output 0 1 2
    typeIdx := some typeIdx }

def exitCode (code : Nat) : Program :=
  [.localGet code, .wrapI64, .call 2, .unreachable]

end Verified.Wasi
