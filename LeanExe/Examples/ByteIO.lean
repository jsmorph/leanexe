import LeanExe.ByteIO
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

end LeanExe.Examples.ByteIO
