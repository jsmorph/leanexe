import LeanExe.ByteIO
import LeanExe.Float32
import LeanExe.Float64
import LeanExe.Runtime

namespace LeanExe.Examples.ByteIO

open LeanExe.ByteIO

def echo : LeanExe.ByteIO UInt32 := do
  match ← read 4 1000000000 with
  | .error code => pure code
  | .ok bytes => write bytes 1000000000

def ordered : LeanExe.ByteIO UInt32 := do
  let code ← write "A".toUTF8 1000000000
  if code != 0 then return code
  write "B".toUTF8 1000000000

def timeout : LeanExe.ByteIO UInt32 := do
  match ← read 4 50000000 with
  | .error code => pure code
  | .ok _ => write "unexpected".toUTF8 1000000000

def handled : LeanExe.ByteIO UInt32 := do
  match ← read 4 50000000 with
  | .error code =>
      if code == 73 then write "timeout".toUTF8 1000000000 else pure code
  | .ok _ => write "read".toUTF8 1000000000

def reused : LeanExe.ByteIO UInt32 := do
  let action := read 1 1000000000
  match ← action with
  | .error code => pure code
  | .ok first =>
      match ← action with
      | .error code => pure code
      | .ok second =>
          let code ← write first 1000000000
          if code != 0 then return code
          write second 1000000000

def unused : LeanExe.ByteIO UInt32 := do
  let _action := write "unexpected".toUTF8 1000000000
  write "ok".toUTF8 1000000000

def ignored : LeanExe.ByteIO UInt32 := do
  let _ ← write "A".toUTF8 1000000000
  write "B".toUTF8 1000000000

def invalid : LeanExe.ByteIO UInt32 := do
  match ← read 0 1000000000 with
  | .error code => pure code
  | .ok _ => pure 99

def immediate : LeanExe.ByteIO UInt32 := do
  match ← read 4 0 with
  | .error code => pure code
  | .ok bytes => write bytes 0

def blocked : LeanExe.ByteIO UInt32 :=
  write (ByteArray.mk (Array.replicate 1048576 65)) 50000000

def emptyWrite : LeanExe.ByteIO UInt32 :=
  write ByteArray.empty 0

def maxTimeout : LeanExe.ByteIO UInt32 := do
  match ← read 4 18446744073709551615 with
  | .error code => pure code
  | .ok bytes => write bytes 18446744073709551615

def helper (bytes : ByteArray) : LeanExe.ByteIO UInt32 :=
  write bytes 1000000000

def called : LeanExe.ByteIO UInt32 := do
  let _ ← helper "A".toUTF8
  helper "B".toUTF8

def repeated : LeanExe.ByteIO UInt32 := do
  for _ in [:3] do
    let _ ← write "x".toUTF8 1000000000
    pure ()
  pure 0

def discardRead : LeanExe.ByteIO UInt32 := do
  let _ ← read 1 1000000000
  match ← read 1 1000000000 with
  | .error code => pure code
  | .ok bytes => write bytes 1000000000

def ignoreReadError : LeanExe.ByteIO UInt32 := do
  let _ ← read 0 0
  write "ok".toUTF8 1000000000

def consume : LeanExe.ByteIO UInt32 := do
  let _ ← read 1 1000000000
  pure 0

def released : LeanExe.ByteIO UInt32 := do
  let _ ← consume
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then 0 else 99)

def copyChecked (timeoutNs : UInt64) : LeanExe.ByteIO UInt32 := do
  let mut running := true
  let mut status : UInt32 := 0
  while running do
    if LeanExe.Runtime.allocCount != LeanExe.Runtime.freeCount then
      status := 98
      break
    match ← read 4096 timeoutNs with
    | .error code =>
        status := code
        running := false
    | .ok bytes =>
        if bytes.size == 0 then
          running := false
        else
          status ← write bytes timeoutNs
          if status != 0 then running := false
  pure status

def streaming : LeanExe.ByteIO UInt32 := do
  let status ← copyChecked 1000000000
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then status else 99)

def alternatingReads : LeanExe.ByteIO UInt32 := do
  let mut status : UInt32 := 0
  for i in [:4] do
    if LeanExe.Runtime.allocCount != LeanExe.Runtime.freeCount then return 98
    if i % 2 == 0 then
      match ← read 1 1000000000 with
      | .error code => status := code
      | .ok bytes => status ← write bytes 1000000000
    if status != 0 then break
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then status else 99)

def streamingTimeout : LeanExe.ByteIO UInt32 := do
  let status ← copyChecked 50000000
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then status else 99)

def carryReads : LeanExe.ByteIO UInt32 := do
  match ← read 1 1000000000 with
  | .error code => pure code
  | .ok initial =>
      let mut previous := initial
      let mut status : UInt32 := 0
      for i in [:8] do
        if i > 1 && i % 2 == 0 then
          match ← read 1 1000000000 with
          | .error code =>
              status := code
              break
          | .ok bytes =>
              status ← write previous 1000000000
              if status != 0 then break
              previous := bytes
      if status != 0 then return status
      status ← write previous 1000000000
      if status != 0 then return status
      write initial 1000000000

def carried : LeanExe.ByteIO UInt32 := do
  let status ← carryReads
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then status else 99)

def nestedCopy (steps : Nat) : LeanExe.ByteIO UInt32 := do
  match ← read 1 50000000 with
  | .error code => pure code
  | .ok initial =>
      for _ in [:2] do
        let mut previous := initial
        for _ in [:steps] do
          match ← read 1 50000000 with
          | .error code => return code
          | .ok bytes =>
              let status ← helper previous
              if status != 0 then return status
              previous := bytes
        let status ← helper previous
        if status != 0 then return status
      helper initial

def nestedReleased : LeanExe.ByteIO UInt32 := do
  let status ← nestedCopy 2
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then status else 99)

def nestedSkipped : LeanExe.ByteIO UInt32 := do
  let status ← nestedCopy 0
  pure (if LeanExe.Runtime.allocCount == LeanExe.Runtime.freeCount then status else 99)

def writeLiteral : LeanExe.ByteIO UInt32 :=
  write "ABC".toUTF8 1000000000

def literalReleased : LeanExe.ByteIO UInt32 := do
  for _ in [:3] do
    let status ← writeLiteral
    if LeanExe.Runtime.allocCount != LeanExe.Runtime.freeCount then return 99
    if status != 0 then return status
  pure 0

def mark (bytes : ByteArray) : LeanExe.ByteIO Unit := do
  let _ ← write bytes 1000000000
  pure ()

def chosen : LeanExe.ByteIO UInt32 := do
  match ← read 1 1000000000 with
  | .error code => pure code
  | .ok bytes =>
      if bytes.size == 0 then mark "A".toUTF8 else mark "B".toUTF8
      mark "C".toUTF8
      pure 0

/-- Dynamic NaN payloads must use the same canonical arithmetic result as the
ordinary Wasmtime host, including signaling and negative inputs. -/
def float32NaNs : LeanExe.ByteIO UInt32 := do
  match ← read 1 1000000000 with
  | .error code => pure code
  | .ok bytes =>
      let bits := (0x7f800000 : UInt32) + bytes[0]!.toUInt32
      pure (if LeanExe.Float32.addBits bits 0x3f800000 == 0x7fc00000 &&
        LeanExe.Float32.addBits (bits ||| 0x00400000) 0x3f800000 == 0x7fc00000 &&
        LeanExe.Float32.addBits (bits ||| 0x80000000) 0x3f800000 == 0x7fc00000
        then 0 else 99)

def float64NaNs : LeanExe.ByteIO UInt32 := do
  match ← read 1 1000000000 with
  | .error code => pure code
  | .ok bytes =>
      let bits := (0x7ff0000000000000 : UInt64) + bytes[0]!.toUInt64
      pure (if LeanExe.Float64.addBits bits 0x3ff0000000000000 == 0x7ff8000000000000 &&
        LeanExe.Float64.addBits (bits ||| 0x0008000000000000) 0x3ff0000000000000 == 0x7ff8000000000000 &&
        LeanExe.Float64.addBits (bits ||| 0x8000000000000000) 0x3ff0000000000000 == 0x7ff8000000000000
        then 0 else 99)

end LeanExe.Examples.ByteIO
